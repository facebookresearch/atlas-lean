# SLOW-APSP computes shortest-path weights

Let $W$ and $L^{(0)}$ be $n \times n$ matrices
over the min-plus semiring on $\mathbb{Z} \cup \{\infty\}$, and let $w_{xy}$ be the underlying value
in $\mathbb{Z} \cup \{\infty\}$ of $W_{xy}$. Suppose that $w_{ii} = 0$ for every $i$, that the
underlying value of $L^{(0)}_{ij}$ is $0$ if $i = j$ and $\infty$ otherwise, and that $w$ has no
negative cycle. Then for all $i, j \in \{0, \dots, n-1\}$, the underlying value $d$ of the
$(i, j)$ entry of the matrix returned by SLOW-APSP on $W$ and $L^{(0)}$ is at most the weight of
every path from $i$ to $j$, and $d$ is either $\infty$ or the weight of some path from $i$ to $j$.
Here a path from $i$ to $j$ is a nonempty sequence of vertices that starts at $i$, ends at $j$ and
has $w_{xy} \ne \infty$ for each pair of consecutive vertices $x, y$; its weight is the sum of
these $w_{xy}$. A negative cycle is a path from a vertex to itself with at least two vertices,
negative weight, and no repeated vertex once its last vertex is removed.
