# APPROX-TSP-TOUR on a given minimum spanning tree costs at most twice any tour

Let $d$ be a
cost function on vertices with values in a linearly ordered additive commutative monoid that is
symmetric, zero on the diagonal, nonnegative and satisfies the triangle inequality. Let $V$ be a
list of vertices, let the tree with root $r$ and subtree forest $F$ be a minimum spanning tree of
$V$ for $d$, and let $H$ be a tour of $V$. Then the cost under $d$ of the closed tour returned by
`APPROX-TSP-TOUR` on $r$ and $F$ is at most twice the cost under $d$ of the closed tour $H$.

## Sources

- CLRS, third edition, Theorem 35.2.
