# Geometric spanner

Let $P$ be a finite set of points in $\mathbb{R}^d$ and $t \ge 1$. A *$t$-spanner* for $P$ is a graph $G$ with vertex set $P$ whose edges are weighted by Euclidean length such that

$$\|x - y\| \le \delta_G(x, y) \le t\,\|x - y\| \qquad\text{for all } x, y \in P,$$

where $\delta_G(x, y)$ is the length of a shortest path from $x$ to $y$ in $G$. The number $t$ is the *stretch factor*.

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 17, "Low-Stretch Spanners": the definition of a $t$-spanner and its stretch factor
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 12, the definition of a $t$-spanner of the Euclidean graph
