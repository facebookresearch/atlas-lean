# Complexity of the planar Voronoi diagram

Let $P$ be a set of $n \ge 3$ sites in $\mathbb{R}^2$. Then $\mathrm{Vor}(P)$ has at most $2n - 5$ vertices and at most $3n - 6$ edges, counting edges that are segments, rays or whole lines.

If the sites lie on one line, the diagram consists of $n - 1$ parallel lines and has no vertices. Otherwise let $v$ and $e$ be the numbers of vertices and edges and $u \ge 3$ the number of unbounded edges, which are rays, one between each two consecutive unbounded cells. Take a circle containing all vertices in its interior, let $q_1, \dots, q_u$ be the points where the rays leave it, in circular order, and replace each ray by the segment from its vertex to its $q_j$; the chords $q_j q_{j+1}$ (indices mod $u$) lie in the interiors of the convex unbounded cells. This gives a simple straight-line plane graph, connected because each clipped cell boundary is a closed curve, adjacent cells share an edge and every unbounded cell's boundary contains a chord, with $v + u$ vertices, $e + u$ edges and $n + 1$ faces, so Euler's formula gives $v - e + n = 1$. Every vertex has degree at least $3$, so $2(e + u) \ge 3(v + u)$, and together these give $v \le 2n - 2 - u \le 2n - 5$ and $e = v + n - 1 \le 3n - 6$.

## Depends on

- [Voronoi diagram of a planar point set](voronoi-diagram.md)

## Proof depends on

- [Euler's formula for connected plane graphs](../../../GraphTheory/planar-graphs-and-minors/euler-s-formula-for-connected-plane-graphs.md)
- [Unbounded Voronoi cells and the convex hull](unbounded-voronoi-cells-and-the-convex-hull.md)

## Sources

- *Geometric Algorithms*, course slides, Utrecht University, 2023, "Voronoi diagrams", <https://ics-websites.science.uu.nl/docs/vakken/ga/2023/slides/slides7_combined.pdf>: slide 13, the theorem that the Voronoi diagram on $n$ sites has at most $2n - 5$ vertices and $3n - 6$ edges, proved with Euler's formula after attaching the unbounded edges to a vertex at infinity (slides 13–17), which gives a multigraph; the clipping argument here reduces to simple plane graphs
- F. Aurenhammer, "Voronoi diagrams — a survey of a fundamental geometric data structure", *ACM Computing Surveys* 23(3), 1991, p. 347: the region count, the unbounded regions of sites on the convex hull boundary, and the bounds on edges and vertices from Euler's relation
