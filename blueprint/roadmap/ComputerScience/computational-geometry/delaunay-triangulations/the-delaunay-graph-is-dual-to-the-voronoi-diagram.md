# The Delaunay graph is dual to the Voronoi diagram

Let $P$ be a set of $n \ge 3$ points in $\mathbb{R}^2$, not all on one line. The *Delaunay graph* of $P$ has vertex set $P$ and an edge $p_i p_j$, drawn as a straight segment, whenever the Voronoi cells $V(p_i)$ and $V(p_j)$ share an edge. The Delaunay graph is a plane graph, its bounded faces correspond to the vertices of $\mathrm{Vor}(P)$, and when no four points of $P$ lie on a common circle it is a triangulation of $P$, namely a Delaunay triangulation.

## Depends on

- [Voronoi diagram of a planar point set](../voronoi-diagrams/voronoi-diagram.md)
- [Delaunay triangulation](delaunay-triangulation.md)

## Proof depends on

- [Empty circle property of Voronoi vertices and edges](../voronoi-diagrams/empty-circle-property-of-voronoi-vertices-and-edges.md)

## Sources

- *Geometric Algorithms*, course slides, Utrecht University, 2023, "Delaunay triangulations", <https://ics-websites.science.uu.nl/docs/vakken/ga/2023/slides/slides9.pdf>: slides 18–21: the Delaunay graph as the straight-line embedding of the dual of $\mathrm{Vor}(P)$, the theorem that it is a plane graph, and that for points in general position it is a triangulation
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 12, the Delaunay triangulation as the dual of the Voronoi diagram
