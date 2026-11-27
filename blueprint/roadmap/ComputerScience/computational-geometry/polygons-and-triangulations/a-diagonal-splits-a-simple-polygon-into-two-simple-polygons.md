# A diagonal splits a simple polygon into two simple polygons

Let $P = p_0 p_1 \cdots p_{n-1}$ be a simple polygon with $n \ge 4$ vertices and let $d = p_0 p_i$, with $2 \le i \le n - 2$, be an interior diagonal. Then $P^+ = p_0 p_i p_{i+1} \cdots p_{n-1}$ and $P^- = p_0 p_1 \cdots p_i$ are simple polygons with $n - i + 1$ and $i + 1$ vertices, their interiors are disjoint, and the interior of $P$ is the union of the interiors of $P^+$ and $P^-$ and the relative interior of $d$.

The proof takes a small disk inside $P$ that meets $d$, a point on each side of $d$ in it, and two parallel rays from these points that cross the same edges of $P$ but differ in whether they cross $d$; comparing parities shows that each point lies inside exactly one of $P^+$ and $P^-$.

## Depends on

- [Diagonals and triangulations of a simple polygon](diagonals-and-triangulations-of-a-simple-polygon.md)

## Proof depends on

- [Jordan curve theorem for polygons](jordan-curve-theorem-for-polygons.md)
- [The complement of a simple polygon has at least two components](the-complement-of-a-simple-polygon-has-at-least-two-components.md)

## Sources

- J. Erickson, *Computational Topology*, lecture notes, University of Illinois, 2023, Chapter 1 (Simple polygons), <https://jeffe.cs.illinois.edu/teaching/comptop/2023/notes/01-simple-polygons.pdf>: Section 1.4, proof of the Triangulation Theorem: $P^+$ and $P^-$ are simple, and the diagonal partitions the interior of $P$ into their interiors (the parity argument with the rays $R^+$ and $R^-$)
