# Complexity of a simple line arrangement

Let $\mathcal{A}(L)$ be a simple arrangement of $n$ lines in the plane. Then $\mathcal{A}(L)$ has exactly $\binom{n}{2}$ vertices, $n^2$ edges and $\binom{n}{2} + n + 1$ faces.

For the face count, clip the arrangement to a large rectangle whose interior contains every vertex and meets every line, with no corner on a line. This gives a connected straight-line plane graph with $\binom{n}{2} + 2n + 4$ vertices and $n^2 + 2n + 4$ edges, so Euler's formula gives $\binom{n}{2} + n + 2$ faces: one outside the rectangle, and one for each face of $\mathcal{A}(L)$.

## Depends on

- [Arrangement of lines](arrangement-of-lines.md)

## Proof depends on

- [Euler's formula for connected plane graphs](../../../GraphTheory/planar-graphs-and-minors/euler-s-formula-for-connected-plane-graphs.md)

## Sources

- D. Halperin and M. Sharir, "Arrangements", Chapter 28 of *Handbook of Discrete and Computational Geometry*, 3rd ed., J. E. Goodman, J. O'Rourke and C. D. Tóth (eds.), CRC Press, 2017, <https://doi.org/10.1201/9781315119601>: Section 28.1.1, Theorem 28.1.1 (the maximum number of $k$-dimensional cells, attained exactly by simple arrangements), which for $d = 2$ gives $\binom n2$, $n^2$ and $\binom n2 + n + 1$
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 14, the lemma on the numbers of vertices, edges and faces of a simple arrangement (its proof applies Euler's formula after adding a vertex at infinity; the clipped version above uses it for straight-line plane graphs)
