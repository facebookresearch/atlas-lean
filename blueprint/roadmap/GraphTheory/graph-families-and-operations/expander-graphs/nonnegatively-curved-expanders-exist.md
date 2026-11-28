# Ollivier's Problem T (non-negatively curved expanders)

The statement that there are a natural number $\Delta$ and a real $\rho < 1$ such that for every $N$ there is a connected simple graph $G$ on a finite vertex set with at least $N$ vertices, every degree at most $\Delta$, second lazy-walk eigenvalue at most $\rho$ and non-negative Ollivier–Ricci curvature. Here, with the lazy walk $P(x, y)$, equal to $1/2$ if $x = y$, to $1/(2\deg x)$ if $y$ is adjacent to $x$, and to $0$ otherwise, the second eigenvalue is at most $\rho$ when for every $f : V \to \mathbb{R}$ with $\sum_x \deg(x) f(x) = 0$, $\sum_x \deg(x) f(x) \sum_y P(x, y) f(y) \le \rho \sum_x \deg(x) f(x)^2$, and the curvature is non-negative when for every edge $xy$ some coupling $\pi$ of $P(x, \cdot)$ and $P(y, \cdot)$, a nonnegative function on $V \times V$ with row sums $P(x, \cdot)$ and column sums $P(y, \cdot)$, has $\sum_{u, v} \pi(u, v)\, d(u, v) \le 1$, $d$ the graph distance. Stated here as a proposition; its resolution: [Sparse expanders cannot have non-negative curvature](nonnegatively-curved-expanders-exist-ref.md).

## Sources

- Y. Ollivier, Discrete Ricci curvature: open problems (2008), Problem T, https://www.yann-ollivier.org/rech/publs/problems_curvmarkov.pdf.
