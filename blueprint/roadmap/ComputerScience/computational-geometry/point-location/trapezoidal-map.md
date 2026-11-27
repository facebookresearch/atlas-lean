# Trapezoidal map

Let $S$ be a set of $n$ line segments in $\mathbb{R}^2$ that meet only in common endpoints, with no two distinct endpoints on a common vertical line (so no segment is vertical), and let $R$ be an axis-parallel rectangle containing all of them in its interior. From each endpoint shoot a vertical ray upward and one downward until it first meets a segment of $S$ or the boundary of $R$. The segments of $S$, the boundary of $R$ and these vertical extensions (the *walls*) subdivide $R$ into faces, each a trapezoid with vertical sides or a triangle; this subdivision is the *trapezoidal map* $T(S)$. Each face is determined by a segment or side of $R$ above it, one below it, and a bounding endpoint or side of $R$ on its left and on its right.

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 8, "Trapezoidal Map": the bullet paths from each endpoint and the four entities that determine a trapezoid
