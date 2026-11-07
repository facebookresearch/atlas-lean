# Search of a valid ball tree

Let $t$ be a ball tree satisfying the bounding-sphere
invariant. For all $q, p \in \mathbb{Z}^d$ and every natural number $r$, $p$ is returned by the
similarity search of $t$ with query $q$ and squared radius $r$ if and only if $p$ is one of the
points stored in $t$ and the squared distance from $q$ to $p$ is at most $r$.
