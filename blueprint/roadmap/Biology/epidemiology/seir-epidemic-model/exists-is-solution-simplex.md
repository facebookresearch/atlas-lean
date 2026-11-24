# Forward-global SEIR solutions on the simplex of total N

Let `β, σ, γ ≥ 0` and `N > 0`. For all `S₀, E₀, I₀, R₀ ≥ 0` with `S₀ + E₀ + I₀ + R₀ = N` there is
a [solution](is-solution.md) `(S, E, I, R)` of the SEIR system with `S(0) = S₀`, `E(0) = E₀`,
`I(0) = I₀` and `R(0) = R₀`, whose compartments are nonnegative and sum to `N` at every time
`t ≥ 0`. It is a special case of the
[forward-global nonnegative solutions](exists-is-solution-nonneg.md), and its values at times
`t ≥ 0` are unique ([forward uniqueness](eq-of-initial.md)).
