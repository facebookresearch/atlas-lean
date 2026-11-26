# Zone theorem for line arrangements

Let $L$ be a set of $n$ lines in the plane, no two parallel and no three through a common point, and let $\ell \notin L$ be a line parallel to no line of $L$ and passing through no vertex of $\mathcal{A}(L)$. The *zone* of $\ell$ is the set of faces of $\mathcal{A}(L)$ that $\ell$ intersects. The sum, over the faces of the zone, of the number of edges on the boundary of each face is at most $6n$.

## Depends on

- [Arrangement of lines](arrangement-of-lines.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 14, "Zone Theorem": the total number of edges in all the cells of the zone is at most $6n$, by counting left-bounding and right-bounding edges
- *Geometric Algorithms*, course slides, Utrecht University, 2023, "Arrangements and duality", <https://ics-websites.science.uu.nl/docs/vakken/ga/2023/slides/slides8.pdf>: the zone theorem, stated as $O(m)$ for $m$ lines
