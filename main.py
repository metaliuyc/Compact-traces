from typing import List

from sympy.combinatorics import Permutation, PermutationGroup
from sympy.combinatorics.named_groups import SymmetricGroup
from sympy import symbols, Product, Sum, Symbol, simplify, Rational,expand
from itertools import combinations

variables = {i+1: symbols(f'X_{i+1}') for i in range(1000)}

# SymmetricGroup(n) in Python acts on {0, 1, ..., n-1}, we define S(n) which acts on {1, ..., n}
def S(n):
    group_n = SymmetricGroup(n + 1).stabilizer(0)
    return group_n

# maximal length element in S(n)
def w(n):
    maximal_length_perm = Permutation(1, n)
    if n %2==0:
        for i in range(1, n//2 ):
            maximal_length_perm = Permutation(1+i, n - i) * maximal_length_perm
    elif n%2 !=0:
        for i in range(1, (n - 1)//2 ):
            maximal_length_perm = Permutation(1+i, n - i) * maximal_length_perm
    return(maximal_length_perm)
print(w(8))
        # Create a dictionary to store the symbols

# identity permutation in S(n)
def id(n):
   for g in S(n).elements:
       if all((i ^ g) == i for i in range(n + 1)):
           return g
print(id(3))

# Inverse of a permutation in S(n)
def inverse_of_perm(p, n):
    for g in S(n).elements:
        if p*g == id(n):
            return g
print(inverse_of_perm(Permutation(1,2)(2,3),3))

# define Kottwitz function (f_{n \alpha, s})
def kottwitz_function(n, s, alpha):
    result_sum = 0
    # Generate all subsets of {1, 2, ..., n} with cardinality s
    for subset in combinations(range(1, n + 1), s):
        # Calculate the product Y^I for each subset
        product_Y_I = 1
        for i in subset:
            product_Y_I = product_Y_I * variables[i]  # Assuming Y_i is a list or array of Y values
        # Add the term to the sum
        result_sum += (product_Y_I ** alpha)
    return result_sum
print(kottwitz_function(5, 2, 2))

# In the following we generate partitions of n, length bounded by k:
def partition(n, max_val=None):
    if max_val is None:
        max_val = n
    # Base case: if n is 0, return an empty partition (singleton partition)
    if n == 0:
        return [[]]
    # Initialize the list to store partitions
    partitions = []
    # Iterate through possible values for the next partition element
    for i in range(1, min(max_val, n) + 1):
        # Recursive call to find partitions for the remaining value
        remaining_partitions = partition(n - i, i)
        # Append the current element to each partition in the recursive result
        for p in remaining_partitions:
            partitions.append([i] + p)
    return partitions

# In the following we generate ordered partitions :
def ordered_partitions(n):
    # Base case: if n is 0, return an empty partition (singleton partition)
    if n == 0:
        return [[]]
    # Initialize the list to store partitions
    partitions = []
    # Iterate through possible values for the next partition element
    for i in range(1, n + 1):
        # Recursive call to find partitions for the remaining value
        remaining_partitions = ordered_partitions(n - i)
        # Append the current element to each partition in the recursive result
        for p in remaining_partitions:
            partitions.append([i] + p)
    # Remove empty partitions
    partitions = [p for p in partitions if p]
    # Sort partitions based on the first element of each partition
    partitions.sort(key=lambda x: x[0])
    return partitions

# symmetric partitions
def symmetric_ordered_partitions(n):
    partitions = []
    for p in ordered_partitions(n):
        if p == p[::-1]:
             partitions.append(p)
    return partitions

print(symmetric_ordered_partitions(4))


def partition_to_sets(partition):
    # Initialize variables
    sets_of_integers = []
    current_value = 1
    # Iterate through the partition
    for part_size in partition:
        current_set = set(range(current_value, current_value + part_size))
        sets_of_integers.append(current_set)
        current_value += part_size
    return sets_of_integers

def partition_to_sequences(partition):
    # Initialize variables
    sequences_of_integers = []
    current_value = 1
    # Iterate through the partition
    for part_size in partition:
        current_sequence = list(range(current_value, current_value + part_size))
        sequences_of_integers.append(current_sequence)
        current_value += part_size
    return sequences_of_integers

def parabolic_subgroup(n, p):
    sets = partition_to_sets(p)
    stabilizer = [
        g for g in S(n).elements if all(g(b) in a for a in sets for b in a)
    ]
    return stabilizer

def ll(p):
    length = 0
    n = p.size
    for i in range (n):
        for j in range (i, n):
            if j^p < i^p:
                length = length + 1
    return length

 # representatives in Q\G/P: indeuced from P, Jacquet module at Q!
def minimal_length_representative(n, p, q):
    list_of_representatives = []
    for g in S(n).elements:
        g_min = g
        for h in parabolic_subgroup(n, p):
            for l in parabolic_subgroup(n, q):
                a = h * g * l
                if ll(a)  <ll(g_min) :
                    g_min = a
        list_of_representatives.append(g_min)
    set_of_representatives = set(list_of_representatives)
    return set_of_representatives

def theta_stable_representative(n,p,q):
    set_of_representatives = set()
    for g in minimal_length_representative(n, p, q):
        g_theta = w(n) * g * w(n)
        for h in parabolic_subgroup(n, p):
            for l in parabolic_subgroup(n, q):
                a = h * g_theta * l
                if ll(a)  <ll(g_theta) :
                    g_theta = a
        if g_theta == g:
            set_of_representatives.add(g)
    return set_of_representatives

def theta_stable_borel(n,p,q):
    set_of_representatives = set()
    for g in theta_stable_representative(n, p, q):
        g_act_on_parabolic = set()
        for a in parabolic_subgroup(n,q):
            g_act_on_parabolic.add(g*a*inverse_of_perm(g,n))
        if len(g_act_on_parabolic.intersection(parabolic_subgroup(n,p))) == 1:
            set_of_representatives.add(g)
    return set_of_representatives

def truncated_kottwitz_function(n, s, alpha, q):
    weyl_chamber = partition_to_sets(q)
    k = len(weyl_chamber)
    result_sum = 0
        # Generate all subsets of {1, 2, ..., n} with cardinality s
    for subset in combinations(range(1, n + 1), s):
        product_Y_I = 1
        sum1 = 0
        sum2 = 0
        for i in range(k - 1):
            sum1 = sum1 + len(weyl_chamber[i].intersection(subset))
            sum2 = sum2 + len(weyl_chamber[-(i + 1)].intersection(subset))
            if sum1 <= sum2:
                # If sum1 is not greater than sum2 for the current i, break out of the loop
                break
        else:
            # The else clause of a for loop is executed if the loop completes without encountering a break statement
            # If the loop completes without breaking, it means sum1 > sum2 for all i
            for i in subset:
                product_Y_I = product_Y_I * variables[i]  # Assuming Y_i is a list or array of Y values
            # Add the term to the sum
            result_sum += (product_Y_I ** alpha)
    return result_sum
print(truncated_kottwitz_function(4, 2, 1, [4]))

def exponents_steinberg(p,n):
    exponents = []
    k = len(p)
    for i in range(1,n+1):
        for j in range(k):
            for l in range(p[j]):
                if i == partition_to_sequences(p)[j][l]:
                    exponents.append(Rational(-(1 + p[j])/2  +l +1))
    return(exponents)
print(exponents_steinberg([3],3))

def exponents_modular_character(q,n):
    exponents = []
    k = len(q)
    sum1 = 0
    sum2 = n
    for i in range(1, n + 1):
        for j in range(k):
            for l in range(q[j]):
                if i == partition_to_sequences(q)[j][l]:
                    if l == 0:
                        if j == 0:
                            sum2 = sum2 - q[j]
                            half_sum = (sum1 -  sum2) / 2
                            half_sum = - half_sum
                            exponents.append(Rational(half_sum))
                        else:
                            sum2 = sum2 - q[j]
                            sum1 = sum1 + q[j-1]
                            half_sum = (sum1 - sum2) / 2
                            half_sum = - half_sum
                            exponents.append(Rational(half_sum))
                    else:
                        exponents.append(Rational(half_sum))
    return (exponents)
print(exponents_modular_character([1,1,1],3))

def sign(q,n):
    k = len(q)
    sum = 0
    if k%2 == 0:
        m = k//2
    else:
        m = (k + 1)//2
    for i in range(m):
        sum = sum + q[i]
    if (sum - 1)%2 == 0:
        sign = 1
    else:
        sign = -1
    return sign

# trace of truncated kottwitz function at q, against steinberg induced from p, with sign.
def signed_trace_steinberg_at_q(n, s, alpha, p, q):
    original_expression = truncated_kottwitz_function(n, s, alpha, q)
    t = symbols('t')
    sum = 0
    exponents_1 = exponents_modular_character(q,n)
    exponents_2 = exponents_steinberg(p,n)
    Y = [variables[i] for i in range(1, n + 1)]
    for w in theta_stable_borel(n,p,q):
        index_w = [(i ^ w) - 1 for i in range(1, n + 1)]
        exponents_w = [exponents_2[index] for index in index_w]
        expression_w = [t ** exp for exp in exponents_w]
        substitution_dict_1 = dict(zip(Y, expression_w))
        result_1 = original_expression.subs(substitution_dict_1)
        sum = sum + result_1
    expression_1 = [t ** exp for exp in exponents_1]
    substitution_dict_2 = dict(zip(Y, expression_1))
    result_2 = original_expression.subs(substitution_dict_2)
    result = expand(sum *  sign(q,n))
    return result 
print(signed_trace_steinberg_at_q(3, 1, 1, [1,1,1], [1,1,1]))

# trace of truncated kottwitz function against steinberg induced from p.
def trace_steinberg_p(n, s, alpha, p):
    t = symbols('t')
    sum = 0
    for q in symmetric_ordered_partitions(n):
        sum = sum + signed_trace_steinberg_at_q(n, s, alpha, p, q)
    sum =t**(Rational(alpha*s*(n-s)/2))*sum
    return sum

n = 3
s = 2
alpha = 1
for p in ordered_partitions(n):
    print(p, trace_steinberg_p(n, s, alpha, p))








