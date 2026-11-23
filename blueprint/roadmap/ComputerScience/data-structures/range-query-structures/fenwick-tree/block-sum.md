# Fenwick-tree interval sum of a list

For a list $a$ of elements of a commutative additive
monoid $\alpha$ and a natural number $j$, the interval sum at the one-indexed position $j$ is
the sum of the $\operatorname{lowbit}(j)$ entries of $a$ ending at zero-indexed position
$j - 1$, where $\operatorname{lowbit}(j)$ is the largest power of two dividing $j$ (with
$\operatorname{lowbit}(0) = 0$) and entries past the end of $a$ count as $0$.
