# Empty circle characterization of Delaunay edges

Let $P$ be a set of $n \ge 3$ points in $\mathbb{R}^2$, not all on one line. A *triangulation* of $P$ is a maximal planar subdivision with vertex set $P$: a maximal set of closed segments with endpoints in $P$ that meet only in common endpoints and contain no other point of $P$; its bounded faces are triangles whose union is $\operatorname{conv}(P)$.

Assume no four points of $P$ lie on a common circle. Two points $p, q \in P$ are joined by an edge of the Delaunay triangulation of $P$ if and only if some circle passes through $p$ and $q$ and has no point of $P$ in its interior.

## Depends on

- [Delaunay triangulation](delaunay-triangulation.md)
- [Existence and uniqueness of the Delaunay triangulation](existence-and-uniqueness-of-the-delaunay-triangulation.md)

## Proof depends on

- [The Delaunay graph is dual to the Voronoi diagram](the-delaunay-graph-is-dual-to-the-voronoi-diagram.md)
- [Empty circle property of Voronoi vertices and edges](../voronoi-diagrams/empty-circle-property-of-voronoi-vertices-and-edges.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 12, "Empty circle property" of the Delaunay triangulation
