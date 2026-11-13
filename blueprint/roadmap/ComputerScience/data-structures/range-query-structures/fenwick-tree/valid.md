# Fenwick tree representing a list

A Fenwick tree $t$ over an additive commutative monoid
represents a list $a$ of length $n$ when its stored array has length $n + 1$ (a dummy entry at
index $0$ plus one entry per element of $a$) and, for every $j$ with $1 \le j \le n$, the stored
entry at index $j$ equals the block sum of $a$ at $j$: the sum of the $\operatorname{lowbit}(j)$
entries of $a$ ending at position $j - 1$ (positions counted from $0$), where
$\operatorname{lowbit}(j)$ is the largest power of two dividing $j$.

The underlying list itself is not stored at runtime; it appears only in this specification
relation.
