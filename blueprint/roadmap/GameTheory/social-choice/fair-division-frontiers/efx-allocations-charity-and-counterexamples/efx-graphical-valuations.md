# EFX allocations exist for graphical valuations while EFX orientations are NP-hard

A graphical instance is given by a multigraph $G = (N, E)$ whose vertices are the agents and whose edges are the goods; each good $e = \{i, j\}$ may have positive (monotone) value only to its endpoints $i, j$, and value $0$ to every other agent. For every graphical instance with monotone valuations, a complete EFX allocation exists and can be computed in polynomial time. In contrast, deciding whether a graphical instance admits an EFX orientation (a complete EFX allocation in which every edge is given to one of its endpoints) is NP-complete.

## Proof sketch

Build the allocation in two phases: first compute a partial orientation in which each agent receives at most a carefully chosen subset of incident edges while maintaining EFX, using a matching-like structure on the graph; then distribute the remaining edges to non-endpoint agents (who value them at zero) so that no envy is created towards the bundles of these agents. Hardness of orientations is by reduction from a satisfiability variant, encoding clauses by small gadgets where EFX forces specific orientations.

## Depends on

- [Partial EFX allocation with an unallocated pool](partial-efx-allocation-with-pool.md)
- [Envy-freeness up to any good](../../../not-yet-classified/part-01/indivisible/is-efx.md)

## Proof depends on

- [Partial EFX allocation with an unallocated pool](partial-efx-allocation-with-pool.md)

## Sources

- G. Christodoulou, A. Fiat, E. Koutsoupias, A. Sgouritsa, "Fair allocation in graphs", EC 2023.
