# One min-plus multiplication extends shortest paths by one edge

Let $A$ and $B$ be
$n \times n$ matrices with entries in $\mathbb{Z} \cup \{\infty\}$, viewed in the min-plus
semiring, and let $r$ be a natural number. Suppose that $B_{jj} = 0$ for every $j$, and that for
all $i$ and $j$ the entry $A_{ij}$ is the shortest weight of a path from $i$ to $j$ with at most
$r$ edges for the weight matrix $B$. Then for all $i$ and $j$, the entry $(i, j)$ of the matrix
returned by the matrix accumulator on $A$, $B$ and the accumulator whose entries are all $\infty$
is the shortest weight of a path from $i$ to $j$ with at most $r + 1$ edges for the weight
matrix $B$.

Paths may repeat vertices and edge weights may be negative.
