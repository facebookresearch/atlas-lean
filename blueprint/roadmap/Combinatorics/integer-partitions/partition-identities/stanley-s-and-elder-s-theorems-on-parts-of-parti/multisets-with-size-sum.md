# Multisets of parts with a given size sum

For a list $L$ of pairs of natural numbers, where
the size of a pair $(k, j)$ is $k$, and a natural number $n$, this is the finite set of multisets
of pairs defined by recursion on $L$. For the empty list it is the set containing only the empty
multiset when $n = 0$, and the empty set otherwise. For a list with head $c$ of size $k$ and tail
$L'$, it is the set of all multisets obtained by adding $i$ copies of $c$ to a member of the set
for $L'$ and $n - ik$, where $i$ ranges over the natural numbers with $i \le n$ and $ik \le n$.

When every pair in $L$ has positive size, this is exactly the set of multisets whose elements all
lie in $L$ and whose sizes, counted with multiplicity, sum to $n$.

## Sources

- Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*, INTEGERS 25 (2025), Article A94, Section 1 (`n`-color partitions; helper for `C(m)`).
