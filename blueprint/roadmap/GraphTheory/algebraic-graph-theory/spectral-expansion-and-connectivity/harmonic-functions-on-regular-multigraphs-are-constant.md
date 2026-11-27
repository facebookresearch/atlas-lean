# Maximum principle: harmonic functions on a connected regular multigraph are constant

Let $G$ be a $D$-regular multigraph ($D \ge 1$) on a finite vertex set $V$, given by a rotation map, whose underlying simple graph is connected. If $f : V \to \mathbb{R}$ satisfies $W_G f = f$, that is $f(v) = \frac1D \sum_i f(v[i])$ for every vertex $v$, then $f$ is constant. Equivalently, the only fixed points of the walk operator are the constants, and the eigenvalue $1$ of $W_G$ is simple.

## Proof sketch

Let $v$ maximize $f$. Since $f(v)$ is the average of the values at its neighbours, all of which are at most $f(v)$, every neighbour attains the maximum too. Connectivity propagates the maximum to every vertex.

## Depends on

- [Rotation map of a regular multigraph](../../graph-families-and-operations/zig-zag-product-and-explicit-expanders/rotation-map.md)
- [Spectral expansion, second eigenvalue and edge expansion of a regular multigraph](../../graph-families-and-operations/expander-graph-operations/spectral-expansion-second-eigenvalue-and-edge-expansion.md)

## Sources

- S. Hoory, N. Linial, A. Wigderson, "Expander Graphs and Their Applications", Bulletin of the American Mathematical Society, 2006.
- S. Arora, B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
