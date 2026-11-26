# Intersecting segments are adjacent before they meet

Let $S$ be a set of $n$ closed line segments in $\mathbb{R}^2$ in general position: no segment is vertical, no endpoint of a segment lies on another segment (so two segments meet only in a proper crossing), no three segments pass through a common point, and no two distinct endpoints or intersection points have the same $x$-coordinate. A vertical *sweep line* moves from left to right; at each position it meets a subset of $S$, ordered from bottom to top, and the *events* are the endpoints and the intersection points of segments.

If two segments $s_i, s_j \in S$ intersect in a point $p$, then $s_i$ and $s_j$ are consecutive in the bottom-to-top order along the sweep line just after the event that immediately precedes $p$ in the sweep, and they stay consecutive until the sweep reaches $p$.

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 4, the general position assumptions of Fig. 20 (including that no endpoint lies on another segment) and the lemma justifying the adjacent-segment rule of the plane sweep
- *Geometric Algorithms*, course slides, Utrecht University, 2023, "Line segment intersection for map overlay", <https://ics-websites.science.uu.nl/docs/vakken/ga/2023/slides/slides2a.pdf>: the lemma that two segments can only intersect after they have become neighbours along the sweep line
