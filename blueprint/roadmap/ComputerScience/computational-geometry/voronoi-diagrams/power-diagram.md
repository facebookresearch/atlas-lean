# Power diagram

A *weighted site* is a pair $(p, w)$ of a point $p \in \mathbb{R}^d$ and a real weight $w$. The *power* of a point $x$ with respect to $(p, w)$ is $\|x - p\|^2 - w$; when $w > 0$ it is the power of $x$ with respect to the sphere with centre $p$ and radius $\sqrt w$. For finitely many weighted sites $(p_1, w_1), \dots, (p_n, w_n)$, the *power cell* of $(p_i, w_i)$ is the set of points whose power with respect to $(p_i, w_i)$ is at most their power with respect to every other site, and the *power diagram* is the subdivision of $\mathbb{R}^d$ into power cells. The points of equal power with respect to two sites with distinct centres form a hyperplane (the *power line* of two circles in the plane), so the power cells are convex polyhedra, possibly empty. With all weights equal it is the Voronoi diagram.


## Depends on

- [Voronoi diagram of a planar point set](voronoi-diagram.md)

## Sources

- F. Aurenhammer, "Voronoi diagrams — a survey of a fundamental geometric data structure", *ACM Computing Surveys* 23(3), 1991, <https://doi.org/10.1145/116873.116880>: pp. 355–356, the power distance $\delta^2(x, p) - w$ of weighted sites, the power line of two circles, and Figure 4 (power diagram of seven circles)
