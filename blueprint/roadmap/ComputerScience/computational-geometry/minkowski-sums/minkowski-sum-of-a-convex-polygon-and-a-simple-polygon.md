# Minkowski sum of a convex polygon and a simple polygon

Let $R$ be a convex polygon with $m$ vertices and $P$ a simple polygon with $n$ vertices, both taken as closed regions (the boundary together with its interior). Then $P \oplus R$ has total complexity $O(nm)$: triangulating $P$ into $n - 2$ triangles $T_i$, the sums $T_i \oplus R$ are convex polygons with $O(m)$ edges that form a collection of pseudodisks, whose union has linear complexity in the number of its arcs. The bound is attained up to a constant: a comb-shaped $P$ with teeth farther apart than the diameter of a regular $m$-gon $R$ gives $\Omega(nm)$.

## Depends on

- [Minkowski sum of two convex polygons](minkowski-sum-of-two-convex-polygons.md)
- [Simple polygons](../polygons-and-triangulations/simple-polygons.md)

## Proof depends on

- [Minkowski sum of two convex polygons](minkowski-sum-of-two-convex-polygons.md)
- [Minkowski sums of convex polygons with disjoint interiors are pseudodisks](minkowski-sums-of-disjoint-convex-sets-are-pseudodisks.md)
- [The union of pseudodisks has linear complexity](the-union-of-pseudodisks-has-linear-complexity.md)
- [Triangulation theorem for simple polygons](../polygons-and-triangulations/triangulation-theorem-for-simple-polygons.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 34, the Theorem on the Minkowski sum of a convex $m$-gon and a simple $n$-gon ($O(nm)$) and Fig. 180 (the $\Omega(nm)$ comb)
