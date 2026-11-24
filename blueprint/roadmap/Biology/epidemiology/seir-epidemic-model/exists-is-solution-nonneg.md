# Forward-global nonnegative SEIR solutions for β, σ, γ, N ≥ 0

Let `β, σ, γ, N ≥ 0`. For every nonnegative initial state `(S₀, E₀, I₀, R₀)` there are functions
`S, E, I, R : ℝ → ℝ` forming a [solution of the SEIR system](is-solution.md), with two-sided
derivatives at every `t ≥ 0`, such that `S(0) = S₀`, `E(0) = E₀`, `I(0) = I₀`, `R(0) = R₀` and, for
every `t ≥ 0`, the compartments `S(t), E(t), I(t), R(t)` are nonnegative with total
`S₀ + E₀ + I₀ + R₀`. The quotient `β S I / N` in the equations is read as `0` when `N = 0`, so
`N = 0` is allowed. The epidemiological domain `β ≥ 0`, `σ, γ, N > 0`, `S₀ + E₀ + I₀ + R₀ = N`
is a [special case](exists-is-solution-simplex.md), and the values of the solution at times
`t ≥ 0` are determined by the initial state ([forward uniqueness](eq-of-initial.md)).

Proof: take the maximal solution of the system through `(S₀, E₀, I₀, R₀)` at time `0`, defined on
an open interval `J`, which leaves every compact set at each end of `J`. For `T ≥ 0` in `J` it
stays over `[0, T]` in the compact set `[0, T] × Δ`, where `Δ` is the simplex of nonnegative states
with total `S₀ + E₀ + I₀ + R₀` ([nonnegativity](nonneg-of-has-deriv-at.md) and
[conservation](total-eq-of-has-deriv-at.md) on an interval). If some `T ≥ 0` were not in `J`,
every forward time of `J` would be below `T`, and the solution could not leave `[0, T] × Δ`, a
contradiction.
