# Incremental construction of a line arrangement

Let $L$ be a set of $n$ lines in the plane, no two parallel and no three through a common point. Inserting the lines one at a time in any order, and inserting the $i$-th line by locating the unbounded face where it enters and then walking along it through the faces of the current arrangement, splitting the edges it crosses, constructs a doubly-connected edge list of $\mathcal{A}(L)$ in $O(n^2)$ time and $O(n^2)$ space; the $i$-th insertion takes $O(i)$ time.

## Depends on

- [Arrangement of lines](arrangement-of-lines.md)
- [Doubly-connected edge list](../line-segment-intersection-reporting/doubly-connected-edge-list.md)

## Proof depends on

- [Zone theorem for line arrangements](zone-theorem-for-line-arrangements.md)
- [Complexity of a simple line arrangement](complexity-of-a-simple-line-arrangement.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 14, "Incremental Construction": insertion of the $i$-th line in $O(i)$ time, bounded with the zone theorem, for $O(n^2)$ total time and space
