# Jarvis's march

Let $P$ be a set of $n \ge 3$ points of $\mathbb{R}^2$ with no three on a line, and let $h$ be the number of vertices of $\operatorname{conv}(P)$. *Jarvis's march* (gift wrapping) starts at the point $p_1 \in P$ of least $y$-coordinate, which is a vertex, with a sentinel $p_0 = (-\infty, 0)$. Having found $p_{i-1}$ and $p_i$, it takes as $p_{i+1}$ the point $p_k \in P \setminus \{p_{i-1}, p_i\}$ that minimizes the angle between the ray from $p_{i-1}$ through $p_i$ and the ray from $p_i$ through $p_k$, found with $O(n)$ orientation tests and no computation of angles; it stops when it returns to $p_1$. It outputs exactly the vertices of $\operatorname{conv}(P)$ in counterclockwise order and runs in $O(nh)$ time.

## Depends on

- [Convex hull of a finite planar point set](convex-hull-of-a-finite-planar-point-set.md)
- [Direction of three points](../orientation-and-segment-intersection-tests/direction.md)

## Sources

- T. M. Chan, "Optimal output-sensitive convex hull algorithms in two and three dimensions", *Discrete & Computational Geometry* 16 (1996), 361–368, <https://doi.org/10.1007/BF02712873>: Section 2, Jarvis's march: $h$ wrapping steps, each taking the point that maximizes the angle at the current vertex, $O(n)$ time per step and $O(nh)$ in total
- R. Seidel, "Convex hull computations", Chapter 26 of *Handbook of Discrete and Computational Geometry*, 3rd ed., J. E. Goodman, J. O'Rourke and C. D. Tóth (eds.), CRC Press, 2017, <https://doi.org/10.1201/9781315119601>: Section 26.4, the planar case: the Jarvis march with running time $O(nM)$
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 3, "Gift-Wrapping and Jarvis's March"
