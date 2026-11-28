# EFX allocations exist for graphical valuations while EFX orientations are NP-hard

A graphical instance is given by a graph $G = (N, E)$ without parallel edges whose vertices are the agents and whose edges are the goods. Each agent $i$ has a monotone valuation $v_i : 2^E \to \mathbb{R}_{\ge 0}$, and every edge not incident to $i$ is irrelevant to $i$: $v_i(S \cup \{e\}) = v_i(S)$ for all $S \subseteq E$ and every edge $e \not\ni i$. For every graphical instance a complete EFX allocation exists and can be computed in polynomial time. In contrast, an EFX orientation (a complete EFX allocation in which every edge is given to one of its endpoints) need not exist, and deciding whether one exists is NP-complete.

## Proof sketch

Add zero-value edges to make the graph complete. A greedy procedure first builds a partial EFX orientation in which each agent holds at most one incident edge and values her bundle at least as much as each of her unallocated incident edges. Further rounds maintain these properties until every envied agent values her bundle at least as much as all her unallocated incident edges together, and every unallocated edge between two envied agents has a common safe agent: an unenvied agent who would not be envied by either endpoint even after receiving all of that endpoint's unallocated edges. Each remaining edge is then given to such a safe agent, for whom it is irrelevant. Hardness of orientations is by a reduction from circuit satisfiability, with heavy and light edges forming gadgets whose EFX orientations simulate Boolean gates.

## Depends on

- [Partial EFX allocation with an unallocated pool](partial-efx-allocation-with-pool.md)
- [Envy-freeness up to any good](../../../not-yet-classified/part-01/indivisible/is-efx.md)

## Sources

- G. Christodoulou, A. Fiat, E. Koutsoupias, A. Sgouritsa, "Fair allocation in graphs", EC 2023.
