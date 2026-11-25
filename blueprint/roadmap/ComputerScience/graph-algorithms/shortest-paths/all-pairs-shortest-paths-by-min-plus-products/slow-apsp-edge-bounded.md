# Bounded-edge shortest weights from SLOW-APSP

Let $W$ and $L^{(0)}$ be
$n \times n$ matrices over the min-plus semiring on $\mathbb{Z} \cup \{\infty\}$, and let $w_{xy}$
be the underlying value in $\mathbb{Z} \cup \{\infty\}$ of $W_{xy}$. Suppose that $w_{ii} = 0$ for
every $i$ and that the underlying value of $L^{(0)}_{ij}$ is $0$ if $i = j$ and $\infty$ otherwise.
Then for all $i, j \in \{0, \dots, n-1\}$, the underlying value $d$ of the $(i, j)$ entry of the
matrix returned by SLOW-APSP on $W$ and $L^{(0)}$ is at most the weight of every path from $i$ to
$j$ with at most $n - 1$ edges, and $d$ is either $\infty$ or the weight of such a path. Here a
path from $i$ to $j$ is a nonempty sequence of vertices that starts at $i$, ends at $j$ and has
$w_{xy} \ne \infty$ for each pair of consecutive vertices $x, y$; vertices may repeat, its number
of edges is its number of vertices minus one, and its weight is the sum of these $w_{xy}$.
