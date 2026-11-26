# Computing halfplane discrepancy in quadratic time

The halfplane discrepancy of $n$ points in $[0,1]^2$ can be computed in $O(n^2)$ time. The $O(n)$ lines of the first type are checked directly in $O(n)$ time each. For a line of the second type, through two points $p_i, p_j$, the number of points on or below it equals the number of dual lines on or above the vertex $p_i^* \cap p_j^*$ of the dual arrangement, which is read off in constant time per vertex from the position of $p_i^*, p_j^*$ in the sweep-line status while sweeping the arrangement.

## Depends on

- [Halfplane discrepancy](halfplane-discrepancy.md)

## Proof depends on

- [Lines that maximize halfplane discrepancy](lines-that-maximize-halfplane-discrepancy.md)
- [Point–line duality reverses order and preserves incidence](point-line-duality-reverses-order-and-preserves-incidence.md)
- [Incremental construction of a line arrangement](incremental-construction-of-a-line-arrangement.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 15, "Type-1" and "Type-2" lines and the $O(n^2)$ computation by sweeping the dual arrangement
