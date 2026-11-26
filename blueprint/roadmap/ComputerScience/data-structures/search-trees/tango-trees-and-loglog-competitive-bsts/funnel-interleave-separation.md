# Tight $\Theta(\log\log n)$ gap between Wilber's bounds

For infinitely many $n$ there are access sequences $X \in [n]^m$ with $\mathrm{W2}(X) = \Omega(\log\log n) \cdot \max_T \mathrm{IB}_T(X)$, the maximum over all reference trees $T$; and for every $X$ and every balanced reference tree $P$, $\mathrm{W2}(X) = O\big((\mathrm{IB}_P(X) + n + m)\log\log n\big)$, so the separation is tight.

## Proof sketch

The upper side follows by chaining $\mathrm{W2}(X) = O(\mathrm{OPT}(X) + n)$ from Wilber's second bound with the tango-tree bound $\mathrm{OPT}(X) = O((\mathrm{IB}_P(X) + n + m)\log\log n)$. For the lower side, Lecomte and Weinstein build a recursively shuffled sequence on which every reference tree sees few alternations while the funnels of a constant fraction of accesses alternate $\Omega(\log\log n)$ times.

## Depends on

- [The funnel bound dominates the interleave bound](../wilber-and-funnel-lower-bounds/funnel-dominates-interleave.md)
- [Tango trees are $O(\log\log n)$-competitive](tango-competitiveness.md)
- [Wilber's second lower bound](../wilber-and-funnel-lower-bounds/wilber-second-bound.md)

## Proof depends on

- [The funnel bound dominates the interleave bound](../wilber-and-funnel-lower-bounds/funnel-dominates-interleave.md)
- [Tango trees are $O(\log\log n)$-competitive](tango-competitiveness.md)
- [Wilber's second lower bound](../wilber-and-funnel-lower-bounds/wilber-second-bound.md)

## Sources

- Victor Lecomte, Omri Weinstein, "Settling the Relationship Between Wilber's Bounds for Dynamic Optimality", ESA (2020), arXiv:1912.02858.
