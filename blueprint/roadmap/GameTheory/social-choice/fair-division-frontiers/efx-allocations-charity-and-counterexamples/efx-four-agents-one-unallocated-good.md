# EFX for four additive agents with at most one unallocated good

For every instance with four agents having additive valuations there is a partial EFX allocation leaving at most one good unallocated, with no agent envying the unallocated good. For every $n \ge 2$ and additive valuations there is a partial EFX allocation leaving at most $n - 2$ goods unallocated, again with no agent envying the pool. Both statements extend to nice cancelable valuations, which contain additive, unit-demand, budget-additive and multiplicative valuations. A valuation $v$ is cancelable if $v(S \cup \{g\}) > v(T \cup \{g\})$ implies $v(S) > v(T)$ for $g \notin S \cup T$, and nice cancelable if some cancelable valuation that gives distinct bundles distinct values respects all strict inequalities of $v$.

## Proof sketch

Extend the champion relation from single unallocated goods to sets of goods, allocated or not, and derive structural properties of the resulting champion graphs. For four agents, show that from any EFX allocation with at least two unallocated goods one can reshuffle and reallocate bundles so as to increase the lexicographic potential of the valuation vector while keeping EFX. For $n$ agents, show that from any EFX allocation with at least $n - 1$ unallocated goods one can reach a Pareto-dominating EFX allocation. The arguments use additivity only through cancelability and the existence of a non-degenerate refinement.

## Depends on

- [Partial EFX allocation with an unallocated pool](partial-efx-allocation-with-pool.md)

## Proof depends on

- [EFX with bounded charity: fewer than n goods left unallocated](efx-with-bounded-charity.md)
- [Envy-cycle rotation preserves EFX and weakly improves every agent](envy-cycle-rotation-preserves-efx.md)
- [Envy graph and most envious agent of a partial allocation](envy-graph-most-envious-agent.md)

## Sources

- B. Berger, A. Cohen, M. Feldman, A. Fiat, "Almost Full EFX Exists for Four Agents", AAAI 2022, arXiv:2102.10654.
