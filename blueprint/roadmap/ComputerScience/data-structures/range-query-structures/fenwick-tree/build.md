# Building a Fenwick tree from a list

For a list $a$ of length $n$ over a commutative
additive monoid $\alpha$, the Fenwick tree built from $a$ stores the array of length $n + 1$
whose entry at index $0$ is $0$ and whose entry at each one-indexed position $j$ with
$1 \le j \le n$ is the sum of the $\operatorname{lowbit}(j)$ entries of $a$ ending at
zero-indexed position $j - 1$, where $\operatorname{lowbit}(j)$ is the largest power of two
dividing $j$.

The input is converted to an array once, so each entry read is constant-time and construction
is $O(n \log n)$.
