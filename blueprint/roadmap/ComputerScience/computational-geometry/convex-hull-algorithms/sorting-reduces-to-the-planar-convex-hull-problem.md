# Sorting reduces to the planar convex hull problem

Let $x_1, \dots, x_n$ be $n \ge 3$ distinct real numbers and let $p_i = (x_i, x_i^2)$ be their lifts to the parabola $y = x^2$. Every $p_i$ is a vertex of $\operatorname{conv}\{p_1, \dots, p_n\}$, and listing the vertices counterclockwise starting from the vertex of least $x$-coordinate lists them in increasing order of $x_i$. Consequently, an algorithm that solves the planar convex hull problem in time $T(n)$ yields an algorithm that sorts $n$ distinct reals in time $T(n) + O(n)$.

## Depends on

- [Convex hull of a finite planar point set](convex-hull-of-a-finite-planar-point-set.md)

## Sources

- D. G. Kirkpatrick and R. Seidel, "The ultimate planar convex hull algorithm?", *SIAM Journal on Computing* 15(1) (1986), 287–299, <https://doi.org/10.1137/0215021>: Section 1, Shamos's observation that $n$ real numbers $x$ can be sorted by computing the convex hull of the points $(x, x^2)$
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 3, the reduction from sorting to the convex hull by lifting to the parabola $y = x^2$
