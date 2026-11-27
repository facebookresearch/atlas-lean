# Existence and uniqueness of the Delaunay triangulation

Let $P$ be a set of $n \ge 3$ points in $\mathbb{R}^2$, not all on one line. A *triangulation* of $P$ is a maximal planar subdivision with vertex set $P$: a maximal set of closed segments with endpoints in $P$ that meet only in common endpoints and contain no other point of $P$; its bounded faces are triangles whose union is $\operatorname{conv}(P)$.

If no four points of $P$ lie on a common circle, then $P$ has exactly one Delaunay triangulation, the Delaunay graph of $P$.

## Depends on

- [Delaunay triangulation](delaunay-triangulation.md)

## Proof depends on

- [Lawson's flip algorithm](lawson-s-flip-algorithm.md)
- [The Delaunay graph is dual to the Voronoi diagram](the-delaunay-graph-is-dual-to-the-voronoi-diagram.md)

## Sources

- *Geometric Algorithms*, course slides, Utrecht University, 2023, "Delaunay triangulations", <https://ics-websites.science.uu.nl/docs/vakken/ga/2023/slides/slides9.pdf>: slides 21–22: for points in general position the Delaunay graph is a triangulation, and a triangulation is a Delaunay triangulation exactly when every circumcircle has no point of $P$ in its interior
