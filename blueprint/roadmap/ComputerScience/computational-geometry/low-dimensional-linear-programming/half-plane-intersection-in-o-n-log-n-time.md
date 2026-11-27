# Half-plane intersection in $O(n \log n)$ time

The common intersection of $n \ge 1$ closed half-planes in $\mathbb{R}^2$ is a possibly empty or unbounded convex polyhedron of dimension at most two: it may be a point, a segment, a ray or a line (for example $\{x \le 0\} \cap \{x \ge 0\}$ is the $y$-axis), and when it is two-dimensional it is a convex polygon, possibly unbounded, with at most $n$ edges. It can be computed in $O(n \log n)$ time.

## Sources

- *Geometric Algorithms*, course slides, Utrecht University, 2023, "Casting a polyhedron", <https://ics-websites.science.uu.nl/docs/vakken/ga/2023/slides/slides4a.pdf>: the theorem that the common intersection of $n$ half-planes can be computed in $O(n \log n)$ time and may be empty or a bounded or unbounded convex polygon
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 6, "Halfplane Intersection"
