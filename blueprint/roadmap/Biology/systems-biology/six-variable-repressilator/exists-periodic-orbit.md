# Periodic orbits near a Hopf point, assuming the Hopf theorem

Assume the
[statement of the local Hopf bifurcation theorem](../three-variable-repressilator/hopf-bifurcation-theorem.md)
on `ℝ⁶`. Let `n ∈ ℕ`, `β > 0` and `μ_c > 0` satisfy the [Hopf condition](is-hopf.md) for the loop
gain `a(μ_c)`, where `a` is the [loop gain](../three-variable-repressilator/gain.md), and let
`α_c = μ_c (1 + μ_cⁿ)` and `ω = ω(a(μ_c), β)`, the [Hopf frequency](hopf-freq.md). Then for every
`ε > 0` there are a rate `α` with `|α − α_c| < ε`, a period `T > 0` with `|T − 2π/ω| < ε` and a
solution `γ : ℝ → ℝ⁶` of `γ' = F(γ)`, for the [six-variable field](vector-field.md) with Hill
coefficient `n`, rate `α` and ratio `β`, that is `T`-periodic, not constant, and stays within `ε` of
`(μ_c, …, μ_c)` in the maximum distance.
