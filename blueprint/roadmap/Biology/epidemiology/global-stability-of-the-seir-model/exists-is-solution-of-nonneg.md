# Forward-global solutions in the feasible region (nonnegative rates)

For `β, σ, γ, μ ≥ 0`
and `N ≥ 0` (so `μ = 0`, the closed model of `isSolution_zero_iff`, is included) and every
nonnegative initial state `(S₀, E₀, I₀, R₀)`, the SEIR system with vital dynamics has a solution
with these initial values, with two-sided derivatives at every `t ≥ 0`, whose compartments stay
nonnegative and whose total stays `≤ max N (S₀ + E₀ + I₀ + R₀)` for all `t ≥ 0`.

Proof: run `ode_maximal_solution_exit_compact` (`U = univ`, `t₀ = 0`) on the auxiliary field
`posField` with inflows `β S⁺ I⁺ / N`, `σ E⁺`, `γ I⁺` and `μ N`. Each compartment then solves a
linear equation `u' = a u + b` with `b ≥ 0`, so it stays nonnegative on its own
(`nonneg_of_hasDerivAt_linear`; no cooperative-system argument is needed), and on the
nonnegative orthant `posField` is the SEIR field. The total `P` satisfies `P' = μ (N - P)`, so
`M - P ≥ 0` for `M = max N P(0)`. The maximal solution thus stays in the compact set
`[0, T] ×ˢ feasible` over `[0, T]`; if some `T ≥ 0` were outside its interval, the time
`max c 0` would contradict the forward exit from that set.
