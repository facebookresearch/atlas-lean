# The shadow vertex pivot rule and the smoothed shadow bound

Let $P = \{x \in \mathbb{R}^d : Ax \le b\}$ with $A \in \mathbb{R}^{n \times d}$. Following Dadush–Huiberts, Definition 8, the system $Ax \le b$ (and $P$) is *nondegenerate* if $n \ge d$, every set of $d$ rows of $A$ is a basis (linearly independent), and every vertex of $P$ is tight at exactly $d$ linearly independent inequalities. For linearly independent objectives $u, c$, the *shadow* of $P$ on the plane $W = \mathrm{span}(u, c)$ is the orthogonal projection $\pi_W(P)$, and, following Definition 9, the shadow is *nondegenerate* if $\dim \pi_W(P) = 2$ and every face $F$ of $P$ such that $\pi_W(F)$ is a face of $\pi_W(P)$ with $\dim \pi_W(F) \le 1$ satisfies $\dim \pi_W(F) = \dim F$.

The *shadow vertex* (Gass–Saaty parametric objective) simplex method starts at a vertex of $P$ maximizing $u$ and follows the vertices maximizing $(1 - \lambda) u + \lambda c$ as $\lambda$ increases from $0$ to $1$. If $P$ is nondegenerate and its shadow on $W$ is nondegenerate, the vertices of $P$ maximizing objectives in $W \setminus \{0\}$ correspond bijectively under $\pi_W$ to the vertices of $\pi_W(P)$ (Lemma 10), and from a feasible basis optimal for $u$ the method finds a feasible basis optimal for $c$, or declares unboundedness, within at most $|\mathrm{vertices}(\pi_W(P))|$ pivots (Theorem 12). Nondegeneracy of $P$ alone does not suffice: projecting the simple tetrahedron with vertices $(0,0,0), (1,0,0), (0,1,0), (1/2,1/2,1)$ onto the $xy$-plane, the last vertex maximizes $(e_1 + e_2)/2$ but projects to the interior of an edge of the shadow.

For a smoothed unit program (right-hand side $\mathbf{1}$, so $0 \in P$, and Gaussian $A$) and a fixed plane $W$, both nondegeneracy conditions hold with probability $1$. No such assertion is made when $A$ and $b$ are both perturbed: there $P$ may be empty with positive probability, in which case it has no two-dimensional shadow.

The *shadow bound* $S(n, d, \sigma)$ is the supremum, over $\bar{A} \in \mathbb{R}^{n \times d}$ with rows of norm at most $1$ and fixed $2$-dimensional planes $W$, of the expected number of vertices of the primal shadow $\pi_W(\{x : (\bar{A} + \sigma G) x \le \mathbf{1}\})$, where $G$ has independent standard Gaussian entries. Huiberts–Lee–Zhang, equation (1), instead define the *polar-section shadow size* $S_{\mathrm{e}}(n, d, \sigma)$ as the same supremum of the expected number of edges of $\mathrm{conv}(a_1, \dots, a_n) \cap W$, where $a_1, \dots, a_n$ are the rows of $\bar A + \sigma G$. Under the nondegeneracy conditions, which hold almost surely here, the number of shadow vertices is at most this number of edges, so $S(n, d, \sigma) \le S_{\mathrm{e}}(n, d, \sigma)$; upper bounds on $S_{\mathrm{e}}$ therefore bound $S$, while lower bounds on $S_{\mathrm{e}}$ are not lower bounds on $S$.

## Depends on

- [Gaussian-smoothed linear programs and smoothed pivot complexity](gaussian-smoothed-linear-programs.md)

## Sources

- K. H. Borgwardt, "The Simplex Method: A Probabilistic Analysis", Springer (1987).
- D. A. Spielman, S.-H. Teng, "Smoothed Analysis of Algorithms: Why the Simplex Algorithm Usually Takes Polynomial Time", Journal of the ACM 51 (2004), arXiv:cs/0111050.
- D. Dadush, S. Huiberts, "A Friendly Smoothed Analysis of the Simplex Method", SIAM Journal on Computing 49 (2020), STOC (2018), arXiv:1711.05667, Section 2 (Definitions 8 and 9, Lemmas 10 and 11, Theorem 12).
- S. Huiberts, Y. T. Lee, X. Zhang, "Upper and Lower Bounds on the Smoothed Complexity of the Simplex Method", STOC (2023), TheoretiCS 4 (2025), arXiv:2211.11860, Section 1, equation (1).
