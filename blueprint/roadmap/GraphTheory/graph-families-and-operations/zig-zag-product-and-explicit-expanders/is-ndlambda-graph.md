# $(N, D, \lambda)$-graph given by a rotation map

Let $V$ and $L$ be finite sets, $N = \lvert V\rvert$, and $\mathrm{rot}$ a [rotation map](rotation-map.md) on $V \times L$ with [adjacency matrix](adj-matrix.md) $A$; its multigraph is $\lvert L\rvert$-regular. For a real $\lambda$, $\mathrm{rot}$ describes an $(N, \lvert L\rvert, \lambda)$-graph if $\lambda \ge 0$ and

$$\lVert A x\rVert \le \lvert L\rvert\, \lambda\, \lVert x\rVert \quad \text{for every } x \text{ orthogonal to the constant vector},$$

that is, when $L$ is nonempty, the normalised adjacency matrix $A/\lvert L\rvert$ satisfies $\lVert (A/\lvert L\rvert) x\rVert \le \lambda \lVert x\rVert$ on that complement (O. Reingold, S. Vadhan and A. Wigderson, Ann. of Math. 155 (2002), Definition 2.2 and the convention after it).
