# Exact ensemble-averaged momentum equation

Let `μ` be a probability measure on a space `Ω` of realizations, and let `u(ω, τ, y)` (velocity),
`f(ω, τ, y)` (body force density) and `σ(ω, τ, y)` (Cauchy stress, `σⱼᵢ` the `j`-th traction
component on a surface of unit normal `eᵢ`) be fields on `ℝⁿ⁺¹`, with a constant density `ρ`. Fix a
time `t`, a point `x`, a radius `ε > 0` and a function `B` on `Ω`, and assume:

- every velocity component `uᵢ(·, τ, y)` is square integrable, at every `τ` and `y`, and every
  stress component `σⱼᵢ(·, t, y)` is integrable, at every `y`;
- almost every realization has velocity components differentiable in time at `x` at every time
  within `ε` of `t`, and velocity and stress components differentiable in space at time `t` at
  every point within `ε` of `x`;
- the derivatives at `(t, x)` are almost everywhere strongly measurable in `ω`;
- `B` is integrable and, for almost every realization, bounds the absolute time derivatives of
  the velocity components at `x` for times within `ε` of `t`, and the norms of the space
  derivatives of `uᵢ`, of the products `uⱼ uᵢ` and of `σⱼᵢ` at time `t` within `ε` of `x`;
- almost every realization obeys the momentum law
  `∂ₜ(ρ uⱼ) + ∑ᵢ ∂ᵢ(ρ uⱼ uᵢ - σⱼᵢ) = fⱼ` at `(t, x)`, for every `j`.

Distances in space are measured in the maximum norm. Then for every component `j` the
[ensemble means](ensemble-mean.md) of the velocity and of the [stress](ensemble-mean-stress.md) obey
the same law with the extra divergence of the [Reynolds stress](reynolds-stress.md) `R`:

`∂ₜ(ρ 𝔼[uⱼ]) + ∑ᵢ ∂ᵢ(ρ 𝔼[uⱼ] 𝔼[uᵢ] - 𝔼[σⱼᵢ]) = ∫ fⱼ dμ - ρ ∑ᵢ ∂ᵢ Rⱼᵢ` at `(t, x)`.

No integrability of the body force is assumed: the law makes it almost surely equal to an integrable
function. Constant density does not make the flow incompressible; no continuity equation is assumed.
