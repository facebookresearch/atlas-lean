# Ball-tree search of a built tree

For every list $P$ of points of $\mathbb{Z}^d$, every
query point $q \in \mathbb{Z}^d$ and every $r \in \mathbb{N}$, let $T$ be the ball tree built from
$P$. The search of $T$ for $q$ and $r$ equals the list of points of $T$, from left to right,
filtered to the points $p$ whose squared distance from $q$ is at most $r$, in their order.
