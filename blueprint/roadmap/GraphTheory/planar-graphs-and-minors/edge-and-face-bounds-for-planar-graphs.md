# Edge and face bounds for planar graphs

Let $G$ be a simple graph with $n \ge 3$ vertices and $e$ edges that has a straight-line plane drawing. Then $e \le 3n - 6$, and if $G$ is connected its drawing has at most $2n - 4$ faces. A plane triangulation, a drawing in which every face, the unbounded one included, is bounded by exactly three edges, has exactly $3n - 6$ edges and $2n - 4$ faces.

The proof adds edges until every face is a triangle, counts edge–face incidences as $2e = 3f$, and substitutes into Euler's formula $n - e + f = 2$.

## Depends on

- [Straight-line planar graph](straight-line-planar-drawings/is-planar.md)

## Proof depends on

- [Euler's formula for connected plane graphs](euler-s-formula-for-connected-plane-graphs.md)

## Sources

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "Planar graphs and testing for planarity" (Chapter 14), <https://sarielhp.org/book/chapters/planar.pdf>: Lemma 14.1.5 (at most $3n - 6$ edges and $2n - 4$ faces; a triangulation has exactly $3n - 6$ edges and $2n - 4$ faces) and Lemma 14.1.4
- *Computational Geometry*, lecture notes, ETH Zürich, autumn 2013, Chapter 4 (Plane graphs and the DCEL), <https://ti.inf.ethz.ch/ew/courses/CG13/lecture/Chapter%204.pdf>: Lemma 4.1 (a planar graph on $n \ge 3$ vertices has at most $3n - 6$ edges and at most $2n - 4$ faces)
