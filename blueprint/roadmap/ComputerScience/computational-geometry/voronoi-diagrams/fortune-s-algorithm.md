# Fortune's algorithm

Let $P$ be a set of $n \ge 2$ distinct sites in $\mathbb{R}^2$. Fortune's plane sweep moves a horizontal sweep line downward and maintains the *beach line*, the $x$-monotone curve of points equidistant from the sweep line and the nearest site above it, which consists of parabolic arcs whose breakpoints trace the Voronoi edges; site events insert arcs and circle events, where an arc vanishes, create Voronoi vertices (this description of the events assumes that no site arrives directly below a breakpoint of the beach line). It computes $\mathrm{Vor}(P)$ in $O(n \log n)$ time for every set of $n \ge 2$ distinct sites.

## Depends on

- [Voronoi diagram of a planar point set](voronoi-diagram.md)

## Proof depends on

- [Complexity of the planar Voronoi diagram](complexity-of-the-planar-voronoi-diagram.md)
- [Empty circle property of Voronoi vertices and edges](empty-circle-property-of-voronoi-vertices-and-edges.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 11, "Computing Voronoi Diagrams" and the plane-sweep algorithm with the beach line, site events and circle events
- *Geometric Algorithms*, course slides, Utrecht University, 2023, "Voronoi diagrams", <https://ics-websites.science.uu.nl/docs/vakken/ga/2023/slides/slides7_combined.pdf>: slide 68, the theorem that the Voronoi diagram of $n$ point sites can be computed in $O(n \log n)$ time
