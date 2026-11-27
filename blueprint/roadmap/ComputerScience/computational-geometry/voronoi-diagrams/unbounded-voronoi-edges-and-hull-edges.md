# Unbounded Voronoi edges and hull edges

Let $P$ be a finite set of points in $\mathbb{R}^2$, not all on one line, and $p_i, p_j \in P$. There is an unbounded edge of the Voronoi diagram of $P$ bounding the cells of $p_i$ and $p_j$ if and only if the segment $p_i p_j$ contains no other point of $P$ and lies on the boundary of $\operatorname{conv}(P)$.

## Depends on

- [Voronoi diagram of a planar point set](voronoi-diagram.md)
- [Convex hull of a finite planar point set](../convex-hull-algorithms/convex-hull-of-a-finite-planar-point-set.md)


## Related topics

- [Unbounded Voronoi cells and the convex hull](unbounded-voronoi-cells-and-the-convex-hull.md)

## Sources

- *Computational Geometry*, lecture notes, ETH Zürich, autumn 2013, Chapter 9 (Voronoi diagrams), <https://ti.inf.ethz.ch/ew/courses/CG13/lecture/Chapter%209.pdf>: Lemma 9.9 and its proof with the family of circles centred on the bisector
