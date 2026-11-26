# Half of the vertices of a maximal planar graph have degree at most eight

Let $G$ be a maximal planar graph with $n \ge 4$ vertices, a simple planar graph to which no edge can be added without losing planarity. Then at least $n/2$ vertices of $G$ have degree at most $8$. Indeed every vertex has degree at least $3$: a plane drawing of $G$ is a plane triangulation, every face bounded by a triangle, and a vertex $v$ of degree at most $2$ would lie on a face not bounded by a triangle (degree $0$ or $1$), or on two faces bounded by the same triangle (degree $2$), which forces $G$ to be that triangle, against $n \ge 4$. So if more than $n/2$ vertices had degree at least $9$ the degree sum would be at least $9 \cdot \tfrac n2 + 3 \cdot \tfrac n2 = 6n$, contradicting the bound $6n - 12$.

## Depends on

- [Straight-line planar graph](straight-line-planar-drawings/is-planar.md)

## Proof depends on

- [Planar graphs have a vertex of degree at most five](planar-graphs-have-a-vertex-of-degree-at-most-five.md)
- [Edge and face bounds for planar graphs](edge-and-face-bounds-for-planar-graphs.md)

## Sources

- R. Diestel, *Graph Theory*, 6th ed., Graduate Texts in Mathematics 173, Springer, 2025, Chapter 4 (Planar graphs), <https://diestel-graph-theory.com/>: Proposition 4.2.8 (a plane graph of order at least $3$ is maximally plane if and only if it is a plane triangulation), Lemma 4.2.5 (a plane graph with two faces of the same boundary is a cycle) and Corollary 4.2.10 (at most $3n - 6$ edges)
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 22, proof of the independent-set lemma: the claim that there must be at least $n/2$ vertices of degree eight or less
