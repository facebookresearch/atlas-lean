# Alpha complex

Let $S = \{z_1, \dots, z_n\} \subset \mathbb{R}^2$ be a finite set in general position (no three on a line and no four on a circle), let $V_i$ be the Voronoi cell of $z_i$, and for $\alpha > 0$ let $B_i(\alpha)$ be the closed disk with centre $z_i$ and radius $\alpha$ and $U(\alpha) = \bigcup_i B_i(\alpha)$. The sets $R_i(\alpha) = V_i \cap B_i(\alpha)$ are convex and decompose $U(\alpha)$. The *α-complex* $K(\alpha)$ is the geometric realization of the nerve of $\{R_1(\alpha), \dots, R_n(\alpha)\}$ obtained by mapping each $R_i(\alpha)$ to $z_i$: a set of points spans a simplex of $K(\alpha)$ when the corresponding regions have a common point. Since $R_i(\alpha) \subseteq V_i$, $K(\alpha)$ is a subcomplex of the Delaunay triangulation of $S$, and $K(\alpha) \subseteq K(\beta)$ for $\alpha \le \beta$. The union of its simplices is the *α-shape*.

## Depends on

- [Voronoi diagram of a planar point set](../voronoi-diagrams/voronoi-diagram.md)
- [Delaunay triangulation](delaunay-triangulation.md)
- [Nerve of a family of sets](../../../Topology/algebraic-topology/simplicial-complexes-from-point-clouds/nerve.md)

## Sources

- H. Edelsbrunner, "Alpha shapes — a survey", 2010: Section 2, the paragraphs "Union of disks", "Voronoi and Delaunay" (the Delaunay triangulation as the realization of the nerve of the Voronoi diagram) and "Alpha complex"
