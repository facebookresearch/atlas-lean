# Geodesic triangles in ultrametric BHV tree space can have arbitrarily high dimension

Let $\mathcal{U}_m \subset \mathbb{R}^{\binom{m}{2}}/\mathbb{R}\mathbf{1}$ be the space of ultrametrics (equidistant rooted trees) on $m$ leaves. It is the support of a simplicial fan of dimension $m-2$ whose rays are the clade metrics $D_\sigma$ ($\sigma \subsetneq [m]$, $|\sigma| \ge 2$), with one cone per nested set of clades. Give each cone the right-angled Euclidean metric in the coordinates of its clade rays; the resulting path metric is the ultrametric Billera–Holmes–Vogtmann (BHV) metric. It is CAT(0), so any two points $v, w$ are joined by a unique geodesic $G(v,w)$. For $S \subset \mathcal{U}_m$, the geodesic convex hull $\mathrm{gconv}(S)$ is the smallest set containing $S$ that contains $G(v,w)$ whenever it contains $v$ and $w$. The geodesic triangle of three points $a,b,c$ is $\mathrm{gconv}(a,b,c)$.

**Theorem.** For every positive integer $d$:

1. There is an orthant space (the BHV-type space of a flag simplicial complex) of dimension $2d$ and three points in it whose geodesic triangle contains a $d$-dimensional simplex.
2. There are three ultrametric trees with $2d+2$ leaves whose geodesic triangle in $\mathcal{U}_{2d+2}$ has dimension at least $d$.

So, unlike Euclidean triangles (dimension at most $2$), BHV geodesic triangles have no dimension bound. By contrast, in the tropical metric $\mathcal{U}_m$ is a tropical linear space, hence tropically convex, and tropical triangles $\mathrm{tconv}(a,b,c)$ are always at most $2$-dimensional.

## Expansion

For part 1, take the flag complex $\Omega$ on vertices $\{1,\dots,4d\}$ whose $2d+1$ facets are the windows $\{i+1,\dots,i+2d\}$, $i = 0,\dots,2d$. Place $a = \sum_{i \le 2d} v_i e_i$ (with $v_i = i/2$ for even $i$ and $v_i = 7(i+1)/2$ for odd $i$) and $b = \sum_{i \le 2d} e_i$ in the first orthant, and $c = \sum_{i \le 2d} e_{2d+i}$ in the last. The Owen–Provan description shows that $G(a,c)$ breaks at points $u^1,\dots,u^d$, each in the relative interior of a $(2d-2)$-dimensional orthant. For each $i$, the geodesic $G(b,u^i)$ leaves the first orthant at a unique boundary point $\widetilde u^i$ (with $\widetilde u^1 = u^1$). The $d+1$ points $a, \widetilde u^1, \dots, \widetilde u^d$ lie in $\mathrm{gconv}(a,b,c)$ and in the first orthant, and they are affinely independent. The convex hull of those points is the simplex. Part 2 embeds this construction in tree space: the $4d$ clades $\{1,2\},\{1,2,3\},\dots,\{1,\dots,2d+1\}$ and $\{1,3\},\{1,3,4\},\dots,\{1,3,\dots,2d+2\}$ on $[2d+2]$ realize the same window complex as a subcomplex of the clade fan of $\mathcal{U}_{2d+2}$.

The result matters for geometric statistics of trees. Convex hulls, and "depth" notions built from them, can grow in dimension very quickly in BHV space. This is one motivation for working with tropical convexity, where segments and polytopes behave better.

## Sources

- B. Lin, B. Sturmfels, X. Tang and R. Yoshida, "Convexity in Tree Spaces", arXiv:1510.08797 (2015), <https://doi.org/10.48550/arXiv.1510.08797>. Theorem 3.4 and Corollary 3.5 (high-dimensional geodesic triangles); Theorem 2.2 (Owen–Provan geodesics); Proposition 4.1 (tropical convexity of $\mathcal{U}_m$). Published version: SIAM Journal on Discrete Mathematics 31 (2017) 2015-2038, <https://doi.org/10.1137/16M1079841>.
