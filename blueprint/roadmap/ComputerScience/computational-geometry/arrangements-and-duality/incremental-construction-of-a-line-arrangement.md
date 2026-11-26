# Incremental construction of a line arrangement

Let $L$ be a set of $n \ge 1$ lines in the plane, no two parallel and no three through a common point, and let $B$ be an axis-parallel rectangle that contains all vertices of $\mathcal{A}(L)$ in its interior. The parts of the lines inside $B$ together with the boundary of $B$ form a connected planar straight-line graph whose bounded faces have no holes. Inserting the lines one at a time in any order, and inserting the $i$-th line by locating the face along the boundary of $B$ where it enters and then walking along it through the faces of the current subdivision, splitting the edges it crosses, constructs a doubly-connected edge list of this subdivision in $O(n^2)$ time and $O(n^2)$ space; the $i$-th insertion takes $O(i)$ time. The vertices of $\mathcal{A}(L)$ are the vertices inside $B$, and its unbounded edges and faces are the edges and faces of the subdivision that meet the boundary of $B$.

## Depends on

- [Arrangement of lines](arrangement-of-lines.md)
- [Doubly-connected edge list](../line-segment-intersection-reporting/doubly-connected-edge-list.md)

## Proof depends on

- [Zone theorem for line arrangements](zone-theorem-for-line-arrangements.md)
- [Complexity of a simple line arrangement](complexity-of-a-simple-line-arrangement.md)

## Sources

- D. Halperin and M. Sharir, "Arrangements", Chapter 28 of *Handbook of Discrete and Computational Geometry*, 3rd ed., J. E. Goodman, J. O'Rourke and C. D. Tóth (eds.), CRC Press, 2017, <https://doi.org/10.1201/9781315119601>: Section 28.4.1, the incremental construction of a simple arrangement of lines with a doubly-connected edge list, each insertion walking through the zone of the new line in $O(i)$ time, and Theorem 28.4.1 ($\Theta(n^2)$ time and space)
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 14, "Incremental Construction": insertion of the $i$-th line in $O(i)$ time, bounded with the zone theorem, for $O(n^2)$ total time and space
- *Geometric Algorithms*, course slides, Utrecht University, 2023, "Duality and arrangements", <https://ics-websites.science.uu.nl/docs/vakken/ga/2023/slides/slides8.pdf>: the construction algorithm with input a set $L$ of $n$ lines and output the doubly-connected edge list of the subdivision induced by a bounding box $B(L)$ that contains all vertices of $\mathcal{A}(L)$ in its interior
