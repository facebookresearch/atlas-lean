# Low-degree independent sets in maximal planar graphs

Let $G$ be a maximal planar graph (every face of a plane drawing, the outer one included, is a triangle) with $n \ge 4$ vertices. Then $G$ has an independent set of at least $n/18$ vertices, each of degree at most $8$. Such a set is found in $O(n)$ time by marking every vertex of degree at least $9$ and then repeatedly choosing an unmarked vertex, adding it to the set and marking it and its neighbours.

## Depends on

- [Straight-line planar graph](../../../GraphTheory/planar-graphs-and-minors/straight-line-planar-drawings/is-planar.md)

## Proof depends on

- [Euler's formula for connected plane graphs](../../../GraphTheory/planar-graphs-and-minors/euler-s-formula-for-connected-plane-graphs.md)
- [Half of the vertices of a maximal planar graph have degree at most eight](../../../GraphTheory/planar-graphs-and-minors/half-of-the-vertices-of-a-maximal-planar-graph-have-degree-at-most.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 22, the lemma on an independent set of at least $n/18$ vertices of degree at most eight, with the counting argument from $e = 3n - 6$
