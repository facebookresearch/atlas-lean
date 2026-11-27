# Tango trees are $O(\log\log n)$-competitive

For every access sequence $X$ of length $m$ on $[n]$, the cost of the tango tree is $O\big((\mathrm{OPT}(X) + n)(1 + \log\log n)\big)$. Hence tango trees are $O(\log\log n)$-competitive online BSTs, the first improvement over the trivial $O(\log n)$ competitive ratio.

## Proof sketch

Summing the per-access bound gives cost $O((\sum_t k_t + m)(1 + \log\log n)) = O((\mathrm{IB}_P(X) + n + m)(1 + \log\log n))$. Wilber's first bound gives $\mathrm{IB}_P(X) \le 2\,\mathrm{OPT}(X) + 2n$, and $m \le \mathrm{OPT}(X)$.

## Depends on

- [Tango trees](tango-tree.md)
- [The binary search tree access model](../dynamic-optimality/the-binary-search-tree-access-model.md)

## Proof depends on

- [Cost of a tango-tree access](tango-access-cost.md)
- [Preferred-child changes are counted by the interleave bound](preferred-child-changes-equal-interleave.md)
- [Wilber's first lower bound](../wilber-and-funnel-lower-bounds/wilber-first-bound.md)

## Sources

- Erik D. Demaine, Dion Harmon, John Iacono, Mihai Pătraşcu, "Dynamic Optimality—Almost", SIAM Journal on Computing 37(1) (2007); FOCS (2004).
