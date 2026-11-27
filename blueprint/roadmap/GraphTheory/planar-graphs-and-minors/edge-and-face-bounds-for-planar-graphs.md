# Edge and face bounds for planar graphs

Let $G$ be a simple graph with $n \ge 3$ vertices and $e$ edges that has a straight-line plane drawing. Then $e \le 3n - 6$, and the drawing has at most $2n - 4$ faces. A plane triangulation, a straight-line plane drawing in which no vertex lies in the interior of an edge and the boundary of every face, the unbounded one included, is a cycle of three edges, has exactly $3n - 6$ edges and $2n - 4$ faces.

For connected $G$ with a cycle, every face is bounded by a closed walk of length at least $3$, so counting edge–face incidences gives $2e \ge 3f$, and Euler's formula $n - e + f = 2$ gives $e \le 3n - 6$ and $f \le 2n - 4$; a forest has at most $n - 1 \le 3n - 6$ edges; and for a graph with $c \ge 2$ components, summing $e_i \le 3n_i - 3$ (valid for every component, small ones included) gives $e \le 3n - 3c \le 3n - 6$. For the faces, with $e \ge 2$ the boundary walks of each face have total length at least $3$, so again $2e \ge 3f$ and $f \le 2e/3 \le 2n - 4$; with $e \le 1$ there is one face. A plane triangulation is connected, since each facial boundary is a single cycle, and $2e = 3f$ with Euler's formula gives $e = 3n - 6$ and $f = 2n - 4$.

## Depends on

- [Straight-line planar graph](straight-line-planar-drawings/is-planar.md)

## Proof depends on

- [Euler's formula for connected plane graphs](euler-s-formula-for-connected-plane-graphs.md)

## Sources

- R. Diestel, *Graph Theory*, 6th ed., Graduate Texts in Mathematics 173, Springer, 2025, Chapter 4 (Planar graphs), <https://diestel-graph-theory.com/>: Corollary 4.2.10 (a plane graph with $n \ge 3$ vertices has at most $3n - 6$ edges, and every plane triangulation has exactly $3n - 6$), with Euler's formula, Theorem 4.2.9, for the face counts
- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "Planar graphs and testing for planarity" (Chapter 14), <https://sarielhp.org/book/chapters/planar.pdf>: Lemma 14.1.5 (at most $3n - 6$ edges and $2n - 4$ faces; a triangulation has exactly $3n - 6$ edges and $2n - 4$ faces) and Lemma 14.1.4
- *Computational Geometry*, lecture notes, ETH Zürich, autumn 2013, Chapter 4 (Plane graphs and the DCEL), <https://ti.inf.ethz.ch/ew/courses/CG13/lecture/Chapter%204.pdf>: Lemma 4.1 (a planar graph on $n \ge 3$ vertices has at most $3n - 6$ edges and at most $2n - 4$ faces)
