# A connected regular multigraph with self-loops has an inverse-polynomial spectral gap

Let $G$ be a $D$-regular multigraph on $N$ vertices, given by a rotation map, whose underlying simple graph is connected, and let $\lambda(G)$ be its spectral expansion.

(1) If at least half of the edges at every vertex are self-loops, then $\lambda(G) \le 1 - \frac{1}{2 N^2 D^2}$.

(2) If every vertex carries at least one self-loop, then $\lambda(G)^2 \le 1 - \frac{1}{D N^3}$, hence $\lambda(G) \le 1 - \frac{1}{8 D N^3}$.

These are the inverse-polynomial gaps that start Reingold's algorithm.

## Proof sketch

For (1), every set of at most half the vertices of a connected graph has a leaving edge, so the edge expansion is at least $1/N$; Cheeger's inequality bounds $\lambda_2 \le 1 - 1/(2N^2D^2)$, and the self-loops make $W_G$ positive semidefinite so $\lambda = \lambda_2$. For (2), compare the values of a unit mean-zero function at the two ends of the edges along a path from its maximum to its minimum: some edge carries a jump of order $N^{-3/2}$, and the self-loop at each vertex converts this into a deficit of order $1/(DN^3)$ in $\mathbb{E}(W_G f)^2$.

## Depends on

- [Spectral expansion, second eigenvalue and edge expansion of a regular multigraph](../../graph-families-and-operations/expander-graph-operations/spectral-expansion-second-eigenvalue-and-edge-expansion.md)

## Proof depends on

- [Cheeger's inequality, hard direction](../part-02/conductance-and-cheeger-s-inequality/exists-threshold-cut-le-sqrt.md)
- [The lazy graph: spectral expansion from the second eigenvalue and from edge expansion](../../graph-families-and-operations/expander-graph-operations/lazy-graph-spectral-bounds.md)

## Sources

- O. Reingold, "Undirected Connectivity in Log-Space", Journal of the ACM, 2008.
- S. Arora, B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- S. Hoory, N. Linial, A. Wigderson, "Expander Graphs and Their Applications", Bulletin of the American Mathematical Society, 2006.
