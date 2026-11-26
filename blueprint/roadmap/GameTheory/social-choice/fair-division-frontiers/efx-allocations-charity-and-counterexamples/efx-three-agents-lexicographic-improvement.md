# Lexicographic improvement step for partial EFX allocations of three agents

Let three agents $a, b, c$ have additive valuations and let $X$ be a partial EFX allocation with a nonempty pool. Then there exists a partial EFX allocation $Y$ such that the vector $\bigl(v_a(Y_a), v_b(Y_b), v_c(Y_c)\bigr)$ is lexicographically strictly larger than $\bigl(v_a(X_a), v_b(X_b), v_c(X_c)\bigr)$, after relabeling the agents so that the comparison is taken in a fixed priority order determined by the instance.

## Proof sketch

Pick an unallocated good $g$. If some agent is envied by nobody, give $g$ to her (after envy-cycle rotation) and keep EFX. Otherwise analyse the champion graph on $\{a, b, c\}$: each agent champions $g$ relative to some bundle, and a case analysis over the possible champion graphs (self-champions, 2-cycles, 3-cycles) shows that one can swap minimal envied subsets of bundles plus $g$ along champion arcs, returning surplus goods to the pool, so that the highest-priority affected agent strictly gains while EFX is restored. Additivity is used to compare the values of the minimal envied sets.

## Depends on

- [Partial EFX allocation with an unallocated pool](partial-efx-allocation-with-pool.md)
- [Envy graph and most envious agent of a partial allocation](envy-graph-most-envious-agent.md)

## Proof depends on

- [Envy-cycle rotation preserves EFX and weakly improves every agent](envy-cycle-rotation-preserves-efx.md)
- [Envy graph and most envious agent of a partial allocation](envy-graph-most-envious-agent.md)

## Sources

- B. R. Chaudhury, J. Garg, K. Mehlhorn, "EFX Exists for Three Agents", EC 2020; Journal of the ACM 71(1) (2024), arXiv:2002.05119.
