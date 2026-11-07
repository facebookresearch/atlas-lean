# Ball-tree search is exact

For every ball tree $T$ over $\mathbb{Z}^d$ satisfying the
bounding-sphere invariant, every query point $q \in \mathbb{Z}^d$ and every $r \in \mathbb{N}$, the
search of $T$ for $q$ and $r$ equals the list of points of $T$, from left to right, filtered to
the points $p$ whose squared distance from $q$ is at most $r$, in their order. Pruning against
the bounding spheres loses no point.
