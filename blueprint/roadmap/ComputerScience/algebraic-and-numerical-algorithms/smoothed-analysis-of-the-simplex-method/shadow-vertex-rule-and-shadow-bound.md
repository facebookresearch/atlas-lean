# The shadow vertex pivot rule and the smoothed shadow bound

For a polyhedron $P = \{x \in \mathbb{R}^d : Ax \le b\}$ and linearly independent objectives $u, c$, the *shadow* of $P$ on the plane $W = \mathrm{span}(u, c)$ is the orthogonal projection $\pi_W(P)$. The *shadow vertex* (Gass-Saaty parametric objective) simplex method starts at a vertex of $P$ maximizing $u$ and follows the vertices maximizing $(1 - \lambda) u + \lambda c$ as $\lambda$ increases from $0$ to $1$; when $P$ is nondegenerate (every vertex is tight at exactly $d$ linearly independent constraints) **and its shadow on $W$ is nondegenerate** ($\dim \pi_W(P) = 2$, and every face $F$ of $P$ whose projection is a face of $\pi_W(P)$ of dimension at most $1$ has $\dim \pi_W(F) = \dim F$), these vertices project to consecutive vertices of the polygon $\pi_W(P)$, so the number of pivots is at most the number of vertices of $\pi_W(P)$. Both conditions hold almost surely for smoothed data and a fixed plane. Nondegeneracy of $P$ alone does not suffice: projecting the simple tetrahedron with vertices $(0,0,0), (1,0,0), (0,1,0), (1/2,1/2,1)$ onto the $xy$-plane, the last vertex maximizes $(e_1 + e_2)/2$ but projects to the interior of an edge of the shadow. The *shadow bound* $S(n, d, \sigma)$ is the supremum, over $\bar{A}$ with rows of norm at most $1$ and fixed $2$-dimensional planes $W$, of the expected number of vertices of $\pi_W(\{x : (\bar{A} + \sigma G) x \le \mathbf{1}\})$.

## Depends on

- [Gaussian-smoothed linear programs and smoothed pivot complexity](gaussian-smoothed-linear-programs.md)

## Sources

- K. H. Borgwardt, "The Simplex Method: A Probabilistic Analysis", Springer (1987).
- D. A. Spielman, S.-H. Teng, "Smoothed Analysis of Algorithms: Why the Simplex Algorithm Usually Takes Polynomial Time", Journal of the ACM 51 (2004), arXiv:cs/0111050.
- D. Dadush, S. Huiberts, "A Friendly Smoothed Analysis of the Simplex Method", SIAM Journal on Computing 49 (2020), STOC (2018), arXiv:1711.05667, Section 2 (Definitions 8 and 9, Lemma 10, Theorem 12).
