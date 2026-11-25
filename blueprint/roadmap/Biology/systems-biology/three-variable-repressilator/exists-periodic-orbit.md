# Periodic orbits near a Hopf point, assuming the Hopf theorem

Assume the [statement of the local Hopf bifurcation theorem](hopf-bifurcation-theorem.md) on `ℝ³`.
Let `n ∈ ℕ` and `μ_c > 0` with `a(μ_c) = 2`, where `a` is the [loop gain](gain.md), and let
`α_c = μ_c (1 + μ_cⁿ)`. Then for every `ε > 0` there are a rate `α` with `|α − α_c| < ε`, a period
`T > 0` with `|T − 2π/√3| < ε` and a solution `γ : ℝ → ℝ³` of `γ' = F(γ)`, for the
[repressilator field](vector-field.md) with Hill coefficient `n` and rate `α`, that is `T`-periodic,
not constant, and stays within `ε` of `(μ_c, μ_c, μ_c)` in the maximum distance. A level with
`a(μ_c) = 2` exists only for [`n > 2`](gain-lt-two-of-le-two.md).
