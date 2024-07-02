from pwn import xor
from itertools import product, count


S = [0xb, 0xf, 0x3, 0x2, 0xa, 0xc, 0x9, 0x1, 0x6, 0x7, 0x8, 0x0, 0xe, 0x5, 0xD, 0x4]

ddt = []
for alpha in range(16):
    l = [0 for _ in range(16)]
    for x in range(16) :
        xx = x^alpha
        beta = S[x]^S[xx]
        l[beta]+=1
    ddt.append(l)
for alpha in range(16):
    for beta in range(16):
        ddt[alpha][beta] = ddt[alpha][beta]/16

def get_bit(n,i) :
    return (n >> i)%2

# check if x complies to truncated diff
# truncated diff read from left to right
def complies_to_trunc(n, diff):
    for i in range(4):
        bit = diff[i]
        if bit != -1 :
            if bit != get_bit(n,i) :
                return False
    return True


# truncated diff represented as length 4 array, 0 means 0 diff, 1 means 1 diff, -1 means we don't case
def truncated_prob(alpha, beta, ddt):
    count = 0
    pr = 0
    for alp in range(16):
        if complies_to_trunc(alp,alpha):
            count += 1
            for bet in range(16) : 
                if complies_to_trunc(bet,beta):
                    pr += ddt[alp][bet]
    return pr/count

def sort_truncated_diffs(ddt):
    search_sp = list(product([1,-1,0],repeat=4))
    search_sp =  [x for x in search_sp if x.count(-1)==3]
    res = []
    for alpha in search_sp :
        for beta in search_sp :
            res.append((truncated_prob(alpha,beta,ddt),alpha,beta))
    res.sort(key=lambda tuple: tuple[0])
    res.reverse()
    return res

print(sort_truncated_diffs(ddt)[:80])

def print_table_with_binary_indexes(table):
    # Print the header row
    print("    ", end="")  # offset for the row labels
    for col in range(16):
        print(f'{col:04b}'.rjust(5), end=" ")
    print()

    # Print each row with the row label
    for row in range(16):
        print(f'{row:04b}', end="")  # row label
        for col in range(16):
            print(f'{table[row][col]:>5}', end=" ")
        print()
# print_table_with_binary_indexes(ddt)
