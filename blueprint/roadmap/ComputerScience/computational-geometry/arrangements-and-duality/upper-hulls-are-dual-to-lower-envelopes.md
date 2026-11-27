# Upper hulls are dual to lower envelopes

Let $P$ be a set of $n \ge 3$ points in the plane, not all on one line, with distinct $x$-coordinates, and let $P^* = \{p^* : p \in P\}$. Say that a line of $P^*$ *appears on* the lower envelope of $P^*$ if it attains the minimum over $P^*$ on an interval of positive length; a line that meets the envelope at a single point does not appear on it. The vertices of the upper hull of $P$, in counterclockwise order (from right to left), are exactly the points whose dual lines appear on the lower envelope of $P^*$, in left-to-right order of the envelope; symmetrically for the lower hull and the upper envelope. For example, for $(0,0), (1,0), (2,0), (3,-1)$ the point $(1,0)$ is not a vertex, and its dual line $y = x$ meets the lower envelope only at $x = 0$.

## Depends on

- [Point–line duality](point-line-duality.md)
- [Convex hull of a finite planar point set](../convex-hull-algorithms/convex-hull-of-a-finite-planar-point-set.md)

## Proof depends on

- [Point–line duality reverses order and preserves incidence](point-line-duality-reverses-order-and-preserves-incidence.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 6, "Convex Hulls and Envelopes": the lemma relating the upper (lower) hull of $P$ to the lower (upper) envelope of $P^*$
