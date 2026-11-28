# Rotation invariance of the funnel bound

For a permutation access sequence $X$, let $X^{\perp}$ be the access sequence whose point set is the image of $P(X)$ under the counterclockwise rotation $(x, y) \mapsto (-y, x)$ by $90$ degrees (with coordinates relabeled by rank), so that keys and times exchange roles. Then $\mathrm{W2}(X^{\perp}) = \mathrm{W2}(X) \pm O(m)$. More precisely, $\mathrm{W2}(X)$ equals, up to a factor $2$ and an additive $O(m)$, the number of *z-rectangles* of $P(X)$: quadruples of points $p, q, r, s$ with $q.x < p.x < r.x < s.x$ and $r.y < q.y < s.y < p.y$ whose spanning rectangle $[q.x, s.x] \times [r.y, p.y]$ contains no other point of $P(X)$. This count is invariant under the rotation, which gives the invariance.

## Proof sketch

A rotation maps each z-rectangle $(p, q, r, s)$ to the z-rectangle $(s^{\perp}, p^{\perp}, q^{\perp}, r^{\perp})$, so the count is rotation invariant. Lecomte and Weinstein show $\mathrm{W2}(X) \ge 2\,\mathrm{zRects}(X)$, and conversely that the funnel of each point $p$, which alternates between its two sides about $\kappa_p$ times, yields at least $\lfloor \kappa_p/2 \rfloor - 1$ distinct z-rectangles with $p$ as top corner, one for each run of funnel points on one side enclosed by points on the other side; summing gives $\mathrm{zRects}(X) \ge \mathrm{W2}(X)/2 - O(m)$.

## Depends on

- [Wilber's funnel bound](funnel-bound.md)
- [Point set of an access sequence and touched set of a BST execution](../geometric-view-of-bst-access/access-point-set.md)

## Sources

- Victor Lecomte, Omri Weinstein, "Settling the Relationship Between Wilber's Bounds for Dynamic Optimality", ESA (2020), arXiv:1912.02858.
