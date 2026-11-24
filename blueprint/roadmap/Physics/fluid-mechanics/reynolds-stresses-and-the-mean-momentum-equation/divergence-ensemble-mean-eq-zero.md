# Divergence-free realizations have a divergence-free ensemble mean

Let `μ` be a probability measure on a space `Ω` of realizations and `u(ω, τ, y)` a velocity field on
`ℝⁿ⁺¹`. Fix a time `t`, a point `x`, a radius `ε > 0` and an integrable function `B` on `Ω`, and
assume: every velocity component `uᵢ(·, t, y)` is integrable, at every `y`; almost every realization
has its velocity components differentiable at time `t` at every point within `ε` of `x`; the space
derivatives at `x` are almost everywhere strongly measurable in `ω`; and for almost every
realization their norms at points within `ε` of `x` are at most `B(ω)`. If almost every realization
has `∑ᵢ ∂ᵢ uᵢ = 0` at `(t, x)`, then the [ensemble mean](ensemble-mean.md) has zero divergence
there: `∑ᵢ ∂ᵢ 𝔼[uᵢ] = 0` at `(t, x)`.
