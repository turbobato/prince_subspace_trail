from sage.all import *
from sage.crypto.sbox import SBox
from sage.misc.persist import SagePickler
from sage.misc.persist import SageUnpickler

S = SBox(0xb, 0xf, 0x3, 0x2, 0xa, 0xc, 0x9, 0x1, 0x6, 0x7, 0x8, 0x0, 0xe, 0x5, 0xD, 0x4)

RC0 = 0x0000000000000000
RC1 = 0x13198a2e03707344
RC2 = 0xa4093822299f31d0
RC3 = 0x082efa98ec4e6c89
RC4 = 0x452821e638d01377
RC5 = 0xbe5466cf34e90c6c

RC = [RC0,RC1,RC2,RC3,RC4,RC5]

sp = VectorSpace(GF(2),64)

M0 = matrix(GF(2), [[0,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]])
M1 = matrix(GF(2), [[1,0,0,0],[0,0,0,0],[0,0,1,0],[0,0,0,1]])
M2 = matrix(GF(2), [[1,0,0,0],[0,1,0,0],[0,0,0,0],[0,0,0,1]])
M3 = matrix(GF(2), [[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,0]])
Mh0 = Matrix(block_matrix([[M0,M1,M2,M3],[M1,M2,M3,M0],[M2,M3,M0,M1],[M3,M0,M1,M2]]))
Mh1 = Matrix(block_matrix([[M1,M2,M3,M0],[M2,M3,M0,M1],[M3,M0,M1,M2],[M0,M1,M2,M3]]))
Mpr = block_diagonal_matrix([Mh0,Mh1,Mh1,Mh0])
Mpr = Matrix(Mpr)

def shift_rows(state):
    nibs = [state[4*i:4*i+4] for i in range(16)]
    order = [0, 5, 10, 15, 4, 9, 14, 3, 8, 13, 2, 7, 12, 1, 6, 11]

    combined_vector = vector(GF(2), sum([nibs[i].list() for i in order],[]))
    return combined_vector
            
def linear_layer(state) :
    return shift_rows(Mpr*state)

# M represent the whole linear layer as a matrix
M = matrix(GF(2), [linear_layer(x) for x in sp.basis()]).T 

def parallel_S(state):
    nibs = [state[4*i:4*i+4] for i in range(16)]
    return sp(sum([S(nib.list()) for nib in nibs],[]))

def round_p(state, k, RC) :
    return linear_layer(parallel_S(state))+sp(to_n_bits(64,RC))+sp(to_n_bits(64,k))

round_for_diff = lambda x : round_p(x,0x0,0x0)

def prince_core(pt, k, r):
    pt = sp(to_n_bits(64,pt))
    pt = pt + sp(to_n_bits(64,RC[0]))+sp(to_n_bits(64,k))
    for i in range(1,r+1):
        pt = round(pt,k,RC[i])
    return pt
# TO DO : check if this works

def derivative(f, u):
    return lambda x : f(x) + f(x + u)

def active_sboxes_to_subspace(bits, n):
    """
    Return a subspace of dimension n *k , corresponding
    to full spaces of dim . n where index in bits is one
    and to zero spaces of dim . n where the corresponding
    index is zero and k = len ( bits ).
    """
    vs = VectorSpace(GF(2),n)
    zero_space = vs.subspace([])
    full_space = vs.subspace(identity_matrix(n))
    ls = [zero_space if i == 0 else full_space for i in bits]
    return reduce(lambda a,b : a.direct_sum(b),ls)

def compute_trail(f,U,n):
    """
    Return the subspace trail from U onwards
    
    INPUT :
    - ‘‘f ‘ ‘ -- function ; map from GF (2)^n to GF (2)^n
    - ‘‘U ‘ ‘ -- subspace ; defining the starting point
    - ‘‘n ‘ ‘ -- integer ; dimension of the vector space
    """
    if U.dimension() == n :
        return [U]
    
    vs = VectorSpace(GF(2),n)
    V = []
    for _ in range (int(1.5*n)):
        V += [derivative(f,u)(vs.random_element()) for u in U.basis() + [vs.zero()]]
    V = vs.subspace(V)
    
    return [U] + compute_trail(f,V,n)
    
def one_round_trails(linear_layer,k):
    """
    Return a list of subspace pairs (U , V ) , st U and V
    form a subspace trail through k parallel applications
    of an Sbox without linear structures followed by the
    given linear layer
    INPUT :
    - ‘‘ linear_layer ‘ ‘ -- matrix ; a n * k ‘ times ‘ n * k matrix over GF(2)
    - ‘‘k ‘ ‘ -- integer ; the number of parallel SBoxes
    """
    n = Integer(linear_layer.ncols()/k)
    
    # we have to check 2^k possible initial
    # U = [( u_1 , u_2 , ... , u_k )] , u_i \ in {0 , 1}
    subspaces = []
    for u in range (1,1<<k):
        # compute U from active SBoxes
        u_bits = Integer(u).digits(base=2,padto=k)
        U = active_sboxes_to_subspace(u_bits,n)
        
        # map linear layer over basis vectors
        v_basis = [linear_layer*bi for bi in U.basis()]
        
        # reduce basis to one vector that has a one entry
        # iff at least one of the basis vectors has a one
        # entry at the same position
        v_bits = list(map(lambda bi : reduce(lambda a,b : int(a) | int(b),bi),zip(*v_basis)))

        # reduce bits to one per sbox only
        v_bits = [1 if v_bits[i*n :(i+1)*n] != [0]*n else 0 for i in range(k)]

        # compute V from active SBoxes
        V = active_sboxes_to_subspace(v_bits,n)
        subspaces.append([U,V])
    return subspaces

def algorithm3(f,k,n):
    """
    Return the set of all subspace trails containing W_{i , alpha }
    
    INPUT :
    - ’’f ’’ -- function ; mapping from F_2 ^ n -> F_2 ^ n
    - ’’k ’’ -- integer ; number of parallel S - boxes in f
    - ’’n ’’ -- integer ; dimension of one S - box
    """
    from itertools import product
    
    dim = n*k
    vs = VectorSpace(GF(2),dim)
    
    trails = [[]]
    # simply generate every possible W_ {i , alpha } and compute
    # the corresponding subspace trail
    for i , alpha in product(range(1,k+1),range(1,1<<n)):
        w_i_alpha = vector(GF(2), [0]*(n*(k-i)) + to_n_bits(n, alpha) + [0]*(n*(i-1)))
        W_i_alpha = vs.subspace([w_i_alpha])
        
        trails.append(compute_trail(f, W_i_alpha, dim))
    
    return trails

def to_n_bits(n,x):
    return Integer(x).digits(base=2,padto=n)[::-1]

def vec2int(v):
    return int(''.join(str(x) for x in v),2)

def int2vec(x):
    sp = VectorSpace(GF(2),64)
    return sp(to_n_bits(64,x))

def save_list(in_list,filename):
    res = []
    for l in in_list :
        res.append([list(map(vec2int,x.basis())) for x in l])
    save(res,filename)

def load_list(filename):
    sp = VectorSpace(GF(2),64)
    out_list = load(filename)
    res = []
    for l in out_list:
        res.append([sp.subspace((list(map(int2vec,x)))) for x in l])
    return res

subsp = one_round_trails(M,16)

save_list(subsp,"one_round.sobj")

trails = []
for U, V in subsp :
    trails.append([U,V]+compute_trail(round_for_diff,V,64))

save(trails,'trails.sobj')

