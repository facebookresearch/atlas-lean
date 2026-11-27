# Nearest-neighbour queries in logarithmic time

Let $P$ be a nonempty set of $n$ points in $\mathbb{R}^2$. In expected $O(n \log n)$ time one can build a data structure of size $O(n)$ that, for any query point $q \in \operatorname{conv}(P)$, finds a nearest neighbour of $q$ in $P$ in $O(\log n)$ time. If $P$ is not contained in a line, triangulate the Voronoi diagram restricted to the hull and answer queries by point location in Kirkpatrick's hierarchy. If $P$ lies on a line, sort it along the line; a query point, which then lies on that segment, is located by binary search and compared with its two neighbours in $P$.

## Depends on

- [Voronoi diagram of a planar point set](voronoi-diagram.md)

## Proof depends on

- [Kirkpatrick's point location structure](../point-location/kirkpatrick-s-point-location-structure.md)
- [Randomized incremental Delaunay triangulation](../delaunay-triangulations/randomized-incremental-delaunay-triangulation.md)
- [The Delaunay graph is dual to the Voronoi diagram](../delaunay-triangulations/the-delaunay-graph-is-dual-to-the-voronoi-diagram.md)

## Sources

- *Computational Geometry*, lecture notes, ETH Zürich, autumn 2013, Chapter 9 (Voronoi diagrams), <https://ti.inf.ethz.ch/ew/courses/CG13/lecture/Chapter%209.pdf>: Corollary 9.18 (nearest neighbour search) and Theorem 9.17 (point location in a triangulation in $O(\log n)$ time after $O(n)$ preprocessing)
