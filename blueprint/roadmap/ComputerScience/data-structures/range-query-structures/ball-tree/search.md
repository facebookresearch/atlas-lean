# Ball-tree similarity search

The search of a ball tree $T$ for a query point
$q \in \mathbb{Z}^d$ and a squared radius $r \in \mathbb{N}$ is the accumulating search of $T$ for
$q$ and $r$ started with the empty accumulator.

When $T$ satisfies the bounding-sphere invariant, the search lists exactly the points of $T$
within squared distance $r$ of $q$, from left to right.
