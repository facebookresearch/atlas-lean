# Forward-global nonnegative SIR solutions

For `γ ≥ 0` (any real `β`, `N`) and every
nonnegative initial state `(S₀, I₀, R₀)`, the SIR system has a solution with these initial values,
with two-sided derivatives at every `t ≥ 0`, whose compartments stay nonnegative and keep the
total `S₀ + I₀ + R₀` for all `t ≥ 0`, and along which `S` (resp. `I`) is positive at a time
`t ≥ 0` iff `S₀ > 0` (resp. `I₀ > 0`). The epidemiological domain `β ≥ 0`, `γ > 0`, `N > 0`,
`S₀ + I₀ + R₀ = N` is a special case.

Proof: the maximal solution of `ode_maximal_solution_exit_compact` (`U = univ`, `t₀ = 0`) stays,
over `[0, T] ∩ I`, in the compact set `[0, T] ×ˢ simplex`; if some `T ≥ 0` were not in its open
interval `I`, every forward time of `I` would be `< T`, and the time `max c 0` would contradict
the forward exit from that compact set.
