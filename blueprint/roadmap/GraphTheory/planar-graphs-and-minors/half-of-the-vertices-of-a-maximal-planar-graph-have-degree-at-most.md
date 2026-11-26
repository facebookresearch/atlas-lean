# Half of the vertices of a maximal planar graph have degree at most eight

Let $G$ be a maximal planar graph with $n \ge 4$ vertices, a simple planar graph to which no edge can be added without losing planarity. Then at least $n/2$ vertices of $G$ have degree at most $8$. Indeed every vertex has degree at least $3$, so if more than $n/2$ vertices had degree at least $9$ the degree sum would be at least $9 \cdot \tfrac n2 + 3 \cdot \tfrac n2 = 6n$, contradicting the bound $6n - 12$.

## Depends on

- [Straight-line planar graph](straight-line-planar-drawings/is-planar.md)

## Proof depends on

- [Planar graphs have a vertex of degree at most five](planar-graphs-have-a-vertex-of-degree-at-most-five.md)
- [Edge and face bounds for planar graphs](edge-and-face-bounds-for-planar-graphs.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 22, proof of the independent-set lemma: the claim that there must be at least $n/2$ vertices of degree eight or less
