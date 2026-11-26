# The funnel bound dominates the interleave bound

There is an absolute constant $c$ such that for every $n$, every reference tree $T$ on $[n]$ and every access sequence $X$ of length $m$, $\mathrm{IB}_T(X) \le c\,(\mathrm{W2}(X) + m)$. This settles the relationship between Wilber's two bounds, a question posed by Wilber and by Iacono and Demaine et al.

## Proof sketch

Using the symmetric characterization, each alternation counted at a node $v$ of the reference tree is assigned to an alternation in the funnel of one of the accesses involved, and the assignment is shown to be at most constant-to-one by a planar argument on the staircases that uses rotation invariance to handle the time-like and key-like directions uniformly.

## Depends on

- [Rotation invariance of the funnel bound](funnel-bound-rotation-invariance.md)
- [Wilber's interleave (alternation) bound](interleave-bound.md)

## Proof depends on

- [Rotation invariance of the funnel bound](funnel-bound-rotation-invariance.md)
- [Wilber's interleave (alternation) bound](interleave-bound.md)

## Sources

- Victor Lecomte, Omri Weinstein, "Settling the Relationship Between Wilber's Bounds for Dynamic Optimality", ESA (2020), arXiv:1912.02858.
