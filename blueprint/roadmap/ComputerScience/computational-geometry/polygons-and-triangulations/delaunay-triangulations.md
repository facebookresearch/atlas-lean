# Delaunay triangulations

Let $P$ be a finite set of points in the plane in general position (no three collinear and no four cocircular). A triangulation of $P$ is a Delaunay triangulation, one in which no point of $P$ lies inside the circumcircle of any triangle, if and only if every edge is locally Delaunay. Starting from any triangulation, flipping edges that are not locally Delaunay terminates in the Delaunay triangulation, which is unique, maximizes the minimum angle among all triangulations of $P$, and is the straight-line dual of the Voronoi diagram of $P$.

## Proof depends on

- [Triangulations of simple polygons and the art gallery theorem](triangulations-of-simple-polygons-and-the-art.md)
- [Correctness of SEGMENTS-INTERSECT](../orientation-and-segment-intersection-tests/segments-intersect-ret-eq-true-iff.md)

## Expansion

This page becomes ready once:

- The statement must be checked against the cited sources, which have not been opened

## Sources

- M. de Berg, O. Cheong, M. van Kreveld and M. Overmars, *Computational Geometry: Algorithms and Applications*, 3rd ed., Springer, 2008
