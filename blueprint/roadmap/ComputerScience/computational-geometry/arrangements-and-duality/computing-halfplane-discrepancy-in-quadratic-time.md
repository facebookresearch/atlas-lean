# Computing halfplane discrepancy in quadratic time

The halfplane discrepancy of $n \ge 1$ points in the interior of $[0,1]^2$, no two on a vertical line, no three on a line and none with a coordinate equal to $1/2$, can be computed in $O(n^2)$ time. Under this assumption a point $p$ is the midpoint of $\ell \cap U$ only for chords joining the two sides of $U$ that meet at the corner of $p$'s quadrant, and at most one line through $p$ has this property, so the $O(n)$ lines of the first type are checked directly in $O(n)$ time each. (A point on a midline of $U$ is the midpoint of the chord for a whole interval of directions, on which $\mu(h)$ is constant, so finitely many directions still suffice there.) For a line of the second type, through two points $p_i, p_j$, the number of points on or below it equals the number of dual lines on or above the vertex $p_i^* \cap p_j^*$ of the dual arrangement, which is computed for all vertices in $O(n^2)$ total time from the doubly-connected edge list of the simple dual arrangement: walking along each dual line from left to right, the number of dual lines above it changes by exactly $1$ at each vertex, starting from the order of the lines at $x \to -\infty$, found by sorting the slopes in $O(n \log n)$ time.

## Depends on

- [Halfplane discrepancy](halfplane-discrepancy.md)

## Proof depends on

- [Lines that maximize halfplane discrepancy](lines-that-maximize-halfplane-discrepancy.md)
- [Point–line duality reverses order and preserves incidence](point-line-duality-reverses-order-and-preserves-incidence.md)
- [Incremental construction of a line arrangement](incremental-construction-of-a-line-arrangement.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 15, "Type-1" lines (where the notes count "at most two" such lines per point, hedged) and "Type-2" lines, and the $O(n^2)$ computation by sweeping the dual arrangement
