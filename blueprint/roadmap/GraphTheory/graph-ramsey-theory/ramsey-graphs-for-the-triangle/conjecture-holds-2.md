# Ramsey graphs for the triangle that are locally trees of triangles

For every natural number
$\ell$ there is a finite graph $G$ with at least $\ell$ vertices such that $G \to_2 K_3$, that is,
every colouring of the edges of $G$ with two colours contains a monochromatic triangle, and such
that for every set $S$ of exactly $\ell$ vertices of $G$, some tree of triangles on the vertex set
of $G$ contains every edge of $G$ with both endpoints in $S$.

This follows from Reiher and Rödl's girth Ramsey theorem (Theorem 1.6 with $F = K_3$, $r = 2$,
$n = \ell$), which gives a graph $H$ with $H \to_2 K_3$ in which every set of at most $\ell$
vertices induces a partial $K_3$-forest; such graphs have treewidth at most $2$, hence lie in
trees of triangles ($2$-trees).

## Sources

- C. Reiher and V. Rödl, The girth Ramsey theorem, arXiv:2308.15589, https://arxiv.org/abs/2308.15589. Moved from `OpenConjectures/Combinatorics/TriangleTreeLocalRamsey`.
