# Bentley–Ottmann plane sweep

Let $S$ be a set of $n$ closed line segments in $\mathbb{R}^2$ in general position: no segment is vertical, no endpoint of a segment lies on another segment (so two segments meet only in a proper crossing), no three segments pass through a common point, and no two distinct endpoints or intersection points have the same $x$-coordinate. A vertical *sweep line* moves from left to right; at each position it meets a subset of $S$, ordered from bottom to top, and the *events* are the endpoints and the intersection points of segments.

The Bentley–Ottmann plane sweep keeps the segments that meet the sweep line in a balanced search tree ordered from bottom to top and the future events in a priority queue ordered by $x$-coordinate; whenever two segments become consecutive along the sweep line it schedules their intersection, if it lies to the right of the sweep line, and whenever two segments cease to be consecutive it deletes their pending intersection from the queue, so that the queue holds at most one crossing for each currently consecutive pair, hence $O(n)$ events. It reports all $m$ intersection points of the segments of $S$ in $O((n + m) \log n)$ time and $O(n)$ space, when each intersection point is reported as it is found and not stored.

## Proof depends on

- [Intersecting segments are adjacent before they meet](intersecting-segments-are-adjacent-before-they-meet.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 4, the deletion of the pending event when two segments cease to be adjacent (which keeps the number of events $O(n)$) and the theorem on reporting all $m$ intersections in $O((n + m) \log n)$ time and $O(n)$ space
