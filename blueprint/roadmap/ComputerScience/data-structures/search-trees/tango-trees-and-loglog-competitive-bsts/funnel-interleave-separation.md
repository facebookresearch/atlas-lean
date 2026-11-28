# Tight $\Theta(\log\log n)$ gap between Wilber's bounds

For infinitely many $n$ there are access sequences $X$ on $[n]$ of length $m$ with $\mathrm{W2}(X) = \Omega(\log\log n) \cdot \big(\mathrm{IB}_T(X) + m\big)$ simultaneously for all reference trees $T$; and for every access sequence $X$ of length $m$ and the balanced reference tree $P$, $\mathrm{W2}(X) = O\big((\mathrm{IB}_P(X) + n + m)\log\log n\big)$, so the separation is tight.

## Proof sketch

The upper side follows by chaining $\mathrm{W2}(X) = O(\mathrm{OPT}(X) + n)$ from Wilber's second bound with the tango-tree bound $\mathrm{OPT}(X) = O((\mathrm{IB}_P(X) + n + m)\log\log n)$. For the lower side, Lecomte and Weinstein build hard sequences on geometrically spaced sets of keys $\{i + 1, i + 2, i + 4, i + 8, \dots\}$, each of which forces any reference tree with small alternation count to be very lopsided, and concatenate them so that the average alternation count is low whichever reference tree is chosen, while the funnel bound stays large.

## Depends on

- [Wilber's funnel bound](../wilber-and-funnel-lower-bounds/funnel-bound.md)
- [Wilber's interleave (alternation) bound](../wilber-and-funnel-lower-bounds/interleave-bound.md)

## Proof depends on

- [Tango trees are $O(\log\log n)$-competitive](tango-competitiveness.md)
- [Wilber's second lower bound](../wilber-and-funnel-lower-bounds/wilber-second-bound.md)

## Sources

- Victor Lecomte, Omri Weinstein, "Settling the Relationship Between Wilber's Bounds for Dynamic Optimality", ESA (2020), arXiv:1912.02858.
