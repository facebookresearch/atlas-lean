# The funnel bound dominates the interleave bound

There is an absolute constant $c$ such that for every $n$, every reference tree $T$ on $[n]$ and every access sequence $X$ of length $m$ on $[n]$ in which no key is accessed twice, $\mathrm{IB}_T(X) \le c\,(\mathrm{W2}(X) + m)$. This settles the relationship between Wilber's two bounds, answering Wilber's conjecture and a question of Iacono and of Demaine et al.

## Proof sketch

Lecomte and Weinstein use the recursive structure of the interleave bound: interleaving two access sequences on disjoint key ranges increases the funnel bound by more than the sum of its parts, by an amount that pays for the alternations at the root of $T$. This yields $\mathrm{IB}_T(X) \le \mathrm{W2}(X) + \mathrm{W2}(\overline{X}) + O(m)$, where $\overline{X}$ is the time reversal of $X$. The z-rectangle characterization of the funnel bound, which is invariant under flips and rotations of the point set, then gives $\mathrm{W2}(\overline{X}) = \mathrm{W2}(X) \pm O(m)$.

## Depends on

- [Wilber's interleave (alternation) bound](interleave-bound.md)
- [Wilber's funnel bound](funnel-bound.md)

## Proof depends on

- [Rotation invariance of the funnel bound](funnel-bound-rotation-invariance.md)

## Sources

- Victor Lecomte, Omri Weinstein, "Settling the Relationship Between Wilber's Bounds for Dynamic Optimality", ESA (2020), arXiv:1912.02858.
