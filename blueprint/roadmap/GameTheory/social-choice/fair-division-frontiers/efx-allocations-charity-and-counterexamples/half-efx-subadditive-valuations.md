# One-half EFX exists for subadditive valuations

Let every agent have a monotone subadditive valuation ($v_i(S \cup T) \le v_i(S) + v_i(T)$). Then a complete $\tfrac12$-EFX allocation exists: an allocation $X$ with $v_i(X_i) \ge \tfrac12\, v_i(X_j \setminus \{g\})$ for all agents $i, j$ and goods $g \in X_j$.

## Proof sketch

Run envy-cycle elimination, but whenever an unallocated good is added to the bundle of a source of the envy graph, first discard from that bundle any good whose removal still leaves an envied set, keeping bundles minimal with respect to envy. Subadditivity bounds the value of a minimal envied bundle by twice the owner's valuation of the envied part, which yields the factor one half.

## Depends on

- [Partial EFX allocation with an unallocated pool](partial-efx-allocation-with-pool.md)

## Proof depends on

- [Envy-cycle rotation preserves EFX and weakly improves every agent](envy-cycle-rotation-preserves-efx.md)
- [Envy graph and most envious agent of a partial allocation](envy-graph-most-envious-agent.md)

## Sources

- B. Plaut, T. Roughgarden, "Almost Envy-Freeness with General Valuations", SODA 2018; SIAM Journal on Discrete Mathematics 34(2) (2020).
