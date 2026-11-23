# Existence of solutions of the SEIR system with vital dynamics

For `β ≥ 0`, `σ > 0`,
`γ ≥ 0`, `μ > 0`, `N > 0` and every nonnegative initial state `(S₀, E₀, I₀, R₀)`, there are
`S, E, I, R` solving the system (`IsSolution`) with these initial values; the solution stays in
the feasible region: its compartments are nonnegative and its total is
`≤ max N (S₀ + E₀ + I₀ + R₀)` for all `t ≥ 0` (so `≤ N` when it starts there). This discharges
the `IsSolution` hypothesis of the stability theorems above for every positive initial state.
The hypotheses `σ > 0`, `μ > 0`, `N > 0` are those of the stability theorems; existence itself
only needs them nonnegative (`exists_isSolution_of_nonneg`).
