# Two sign changes of the profile give two roots

Let `k₁, …, kₙ` (`n ≥ 1`) be counts observed at positive size factors `s₁, …, sₙ`, and let `ℓ(a, b)`
be their
[log marginal likelihood](../likelihood-equations-and-efficiency-of-the-gamma/log-marginal-lik.md)
in the shape `a` and the rate `b`. Assume some count is positive, and let `0 < a₁ < a₂ < a₃` be such
that `0` lies between the values of the
[profile shape score along the rate root](profile-shape-score-varying.md) at `a₁` and `a₂`, and
between its values at `a₂` and `a₃` (endpoints included), and the profile does not vanish at `a₂`.
Then the joint score equations have two solutions `(a, b)` and `(a', b')` with `a, b, a', b' > 0`
and `a < a'`: the [shape score](../likelihood-equations-and-efficiency-of-the-gamma/shape-score.md)
`∂ℓ/∂a` and the [rate score](../likelihood-equations-and-efficiency-of-the-gamma/rate-score.md)
`∂ℓ/∂b` both vanish at both.

For example, at size factors `(1000, 1/100, 100)` and counts `(12, 1, 6)` the profile changes sign
twice. These counts satisfy the Pearson-type overdispersion condition `∑ᵢ (kᵢ - sᵢ μ̂)² > ∑ᵢ kᵢ`,
with `μ̂` the [pooled Poisson rate](pooled-mean.md), so the uniqueness of the joint score root at a
common size factor ([exactly one joint score root](exists-unique-score-root-const-varying.md)) does
not extend to heterogeneous size factors.
