# Forward-global nonnegative SEIR solutions

For `β, σ, γ, N ≥ 0` and every nonnegative
initial state `(S₀, E₀, I₀, R₀)`, the SEIR system has a solution with these initial values,
with two-sided derivatives at every `t ≥ 0`, whose compartments stay nonnegative and keep the
total `S₀ + E₀ + I₀ + R₀` for all `t ≥ 0`. The epidemiological domain `β ≥ 0`, `σ, γ, N > 0`,
`S₀ + E₀ + I₀ + R₀ = N` is a special case (`exists_isSolution_simplex`); uniqueness is
`IsSolution.eq_of_initial`.

Proof: the maximal solution of `ode_maximal_solution_exit_compact` (`U = univ`, `t₀ = 0`) stays,
over `[0, T]` inside its interval `J`, in the compact set `[0, T] ×ˢ simplex`
(`nonneg_of_hasDerivAt`, `total_eq_of_hasDerivAt`); if some `T ≥ 0` were not in `J`, the time
`max c 0` would contradict the forward exit from that compact set.
