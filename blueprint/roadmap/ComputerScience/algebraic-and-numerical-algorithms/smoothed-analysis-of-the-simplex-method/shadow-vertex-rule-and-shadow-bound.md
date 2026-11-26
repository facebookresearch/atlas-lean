# The shadow vertex pivot rule and the smoothed shadow bound

For a polyhedron $P = \{x \in \mathbb{R}^d : Ax \le b\}$ and linearly independent objectives $u, c$, the *shadow* of $P$ on the plane $W = \mathrm{span}(u, c)$ is the orthogonal projection $\pi_W(P)$. The *shadow vertex* (Gass-Saaty parametric objective) simplex method starts at a vertex of $P$ maximizing $u$ and follows the vertices maximizing $(1 - \lambda) u + \lambda c$ as $\lambda$ increases from $0$ to $1$; when $P$ is nondegenerate, as holds almost surely for smoothed data, these vertices project to consecutive vertices of the polygon $\pi_W(P)$, so the number of pivots is at most the number of vertices of $\pi_W(P)$. The *shadow bound* $S(n, d, \sigma)$ is the supremum, over $\bar{A}$ with rows of norm at most $1$ and fixed $2$-dimensional planes $W$, of the expected number of vertices of $\pi_W(\{x : (\bar{A} + \sigma G) x \le \mathbf{1}\})$.

## Depends on

- [Gaussian-smoothed linear programs and smoothed pivot complexity](gaussian-smoothed-linear-programs.md)
- [Termination and correctness of the simplex method with Bland's rule](../../graph-algorithms/linear-programming-and-flows/termination-and-correctness-of-the-simplex.md)
- [Basic feasible points are the extreme points](../../../Analysis/not-yet-classified/linear-programming-basic/is-basic-pt-iff-mem-extreme-points.md)

## Sources

- K. H. Borgwardt, "The Simplex Method: A Probabilistic Analysis", Springer (1987).
- D. A. Spielman, S.-H. Teng, "Smoothed Analysis of Algorithms: Why the Simplex Algorithm Usually Takes Polynomial Time", Journal of the ACM 51 (2004), arXiv:cs/0111050.
- D. Dadush, S. Huiberts, "A Friendly Smoothed Analysis of the Simplex Method", SIAM Journal on Computing 49 (2020), STOC (2018), arXiv:1711.05667.
