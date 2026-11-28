# One-half EFX exists for subadditive valuations

Let every agent have a monotone subadditive valuation ($v_i(S \cup T) \le v_i(S) + v_i(T)$). Then a complete $\tfrac12$-EFX allocation exists: an allocation $X$ with $v_i(X_i) \ge \tfrac12\, v_i(X_j \setminus \{g\})$ for all agents $i, j$ and goods $g \in X_j$.

## Proof sketch

Process the goods one at a time, keeping a partial $\tfrac12$-EFX allocation with an acyclic envy graph. Give the next good $g$ to an unenvied agent $j$. If some agent $i$ now violates $\tfrac12$-EFX towards $j$, return $i$'s bundle to the pool and give $i$ the single good $g$ instead. Since $i$ did not violate $\tfrac12$-EFX before, adding $g$ must have at least doubled $i$'s value for a subset of $X_j$, so subadditivity gives $v_i(\{g\}) > v_i(X_i)$; any envy towards $i$ is then fully EFX because $i$ holds one good. Envy cycles are eliminated by rotation. Each round either shrinks the pool or strictly increases $\sum_i v_i(X_i)$, so the process terminates with a complete $\tfrac12$-EFX allocation.

## Depends on

- [Partial EFX allocation with an unallocated pool](partial-efx-allocation-with-pool.md)

## Proof depends on

- [Envy-cycle rotation preserves EFX and weakly improves every agent](envy-cycle-rotation-preserves-efx.md)
- [Envy graph and most envious agent of a partial allocation](envy-graph-most-envious-agent.md)

## Sources

- B. Plaut, T. Roughgarden, "Almost Envy-Freeness with General Valuations", SODA 2018; SIAM Journal on Discrete Mathematics 34(2) (2020).
