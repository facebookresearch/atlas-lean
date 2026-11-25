# FASTER-APSP computes shortest-path weights

Let $W$ be an $n \times n$ matrix with
entries in $\mathbb{Z} \cup \{\infty\}$, read as edge weights of a directed graph on the
vertices $0, \dots, n - 1$ (weight $\infty$ meaning no edge), such that $W_{ii} = 0$ for every
$i$ and $W$ has no negative cycle. Run FASTER-APSP on $W$ over the min-plus semiring, whose
addition is $\min$ and whose multiplication is $+$. Then for all vertices $i$ and $j$, the
returned entry $d$ at $(i, j)$ is the shortest-path weight from $i$ to $j$: $d$ is at most the
weight of every path from $i$ to $j$ all of whose edges have finite weight, and either
$d = \infty$ or $d$ is the weight of such a path. Paths are nonempty vertex sequences and may
repeat vertices.
