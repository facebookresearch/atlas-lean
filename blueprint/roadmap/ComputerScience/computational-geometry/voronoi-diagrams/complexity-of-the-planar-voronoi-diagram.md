# Complexity of the planar Voronoi diagram

Let $P$ be a set of $n \ge 3$ sites in $\mathbb{R}^2$. Then $\mathrm{Vor}(P)$ has at most $2n - 5$ vertices and at most $3n - 6$ edges, counting edges that are segments, rays or whole lines.

## Depends on

- [Voronoi diagram of a planar point set](voronoi-diagram.md)

## Proof depends on

- [Euler's formula for connected plane graphs](../../../GraphTheory/planar-graphs-and-minors/euler-s-formula-for-connected-plane-graphs.md)
- [Edge and face bounds for planar graphs](../../../GraphTheory/planar-graphs-and-minors/edge-and-face-bounds-for-planar-graphs.md)

## Sources

- *Geometric Algorithms*, course slides, Utrecht University, 2023, "Voronoi diagrams", <https://ics-websites.science.uu.nl/docs/vakken/ga/2023/slides/slides7_combined.pdf>: slide 13, the theorem that the Voronoi diagram on $n$ sites has at most $2n - 5$ vertices and $3n - 6$ edges, proved with Euler's formula (slides 13–17)
- F. Aurenhammer, "Voronoi diagrams — a survey of a fundamental geometric data structure", *ACM Computing Surveys* 23(3), 1991, p. 347: the region count, the unbounded regions of sites on the convex hull boundary, and the bounds on edges and vertices from Euler's relation
