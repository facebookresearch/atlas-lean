# Lexicographic improvement step for partial EFX allocations of three agents

Let three agents $a, b, c$ have additive valuations that are non-degenerate, meaning that no agent values two distinct sets of goods equally ($v_i(S) \ne v_i(T)$ whenever $S \ne T$, so in particular every good has positive value to every agent), with agent $a$ fixed arbitrarily in advance, and let $X$ be a partial EFX allocation with a nonempty pool. Then there exists a partial EFX allocation $Y$ such that the vector $\bigl(v_a(Y_a), v_b(Y_b), v_c(Y_c)\bigr)$ is lexicographically strictly larger than $\bigl(v_a(X_a), v_b(X_b), v_c(X_c)\bigr)$: either $Y$ Pareto-dominates $X$, or $v_a(Y_a) > v_a(X_a)$. Non-degeneracy is needed: if every good has value $0$ to every agent, all allocations have the same value vector and no strict improvement exists.

## Proof sketch

Non-degeneracy costs nothing for the final existence of complete EFX allocations: replacing $v_i(g_j)$ by $v_i(g_j) + \varepsilon 2^j$ for a small enough $\varepsilon > 0$ makes any instance non-degenerate and preserves every strict inequality between bundle values, so an EFX allocation of the perturbed instance is EFX for the original one. The perturbation is used only for that final claim; the step itself is proved for the non-degenerate instance. Make the envy graph acyclic by rotating envy cycles and pick an unallocated good $g$. If some agent $i$ champions an agent $s$ from which $i$ is reachable in the envy graph (as happens when the envy graph has a single source or some agent champions herself), give $i$ the bundle $(X_s \setminus G) \cup \{g\}$ for a largest set $G$ she can discard while still envying it, and shift bundles along the envy path from $s$ to $i$; this Pareto-improves while keeping EFX. Otherwise split each championed bundle into an upper and a lower half and analyse the possible champion graphs (2-cycles and 3-cycles); in each case swapping half-bundles yields a Pareto improvement or strictly improves agent $a$ while restoring EFX. Additivity is used to compare the values of half-bundles.

## Depends on

- [Partial EFX allocation with an unallocated pool](partial-efx-allocation-with-pool.md)
- [Envy graph and most envious agent of a partial allocation](envy-graph-most-envious-agent.md)

## Proof depends on

- [Envy-cycle rotation preserves EFX and weakly improves every agent](envy-cycle-rotation-preserves-efx.md)

## Sources

- B. R. Chaudhury, J. Garg, K. Mehlhorn, "EFX Exists for Three Agents", EC 2020; Journal of the ACM 71(1) (2024), arXiv:2002.05119.
