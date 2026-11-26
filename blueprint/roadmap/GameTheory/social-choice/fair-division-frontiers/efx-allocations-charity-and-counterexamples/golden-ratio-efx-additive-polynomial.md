# Polynomial-time (phi - 1)-EFX allocations for additive valuations

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. There is a polynomial-time algorithm that outputs a complete allocation which is simultaneously EF1 and $(\varphi - 1)$-EFX, where $\varphi = (1 + \sqrt5)/2$; that is, $v_i(X_i) \ge (\varphi - 1)\, v_i(X_j \setminus \{g\})$ for all agents $i, j$ and goods $g \in X_j$. The same allocation is $\tfrac{2}{\varphi + 2}$-approximately groupwise maximin share fair.

## Proof sketch

Start by letting agents pick goods in a round-robin fashion for a preprocessing phase that assigns each agent one high-value good, then allocate the remaining goods by envy-cycle elimination in decreasing order of value. The golden ratio arises from balancing two cases: an envied bundle consisting of one large good, controlled by the preprocessing, and a bundle of several smaller goods, controlled by the order in which goods are added.

## Depends on

- [Partial EFX allocation with an unallocated pool](partial-efx-allocation-with-pool.md)
- [Is EF1](../../../not-yet-classified/part-01/indivisible/is-ef1.md)
- [Envy-cycle rotation preserves EFX and weakly improves every agent](envy-cycle-rotation-preserves-efx.md)

## Proof depends on

- [Envy-cycle rotation preserves EFX and weakly improves every agent](envy-cycle-rotation-preserves-efx.md)
- [Round-robin allocation is envy-free up to one good](../../../cooperative-games/fair-division-of-indivisible-goods/round-robin-allocation-is-ef1.md)

## Sources

- G. Amanatidis, E. Markakis, A. Ntokos, "Multiple Birds with One Stone: Beating 1/2 for EFX and GMMS via Envy Cycle Elimination", AAAI 2020; Theoretical Computer Science 841 (2020), arXiv:1909.07650.
