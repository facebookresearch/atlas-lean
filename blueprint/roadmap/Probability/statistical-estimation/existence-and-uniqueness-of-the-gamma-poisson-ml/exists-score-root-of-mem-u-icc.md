# A root of the joint score equations from a sign change of the profile

Let `k₁, …, kₙ` (`n ≥ 1`) be counts observed at positive size factors `s₁, …, sₙ`, and let `ℓ(a, b)`
be their
[log marginal likelihood](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/log-marginal-lik.md)
in the shape `a` and the rate `b`. Assume some count is positive, and let `0 < a₁ ≤ a₂` be such that
`0` lies between the values of the
[profile shape score along the rate root](profile-shape-score-varying.md) at `a₁` and at `a₂` (in
either order, endpoints included). Then some `a ∈ [a₁, a₂]` has positive [rate root](rate-root.md)
`b̂(a) > 0`, and `(a, b̂(a))` solves the joint score equations: the
[shape score](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/shape-score.md) `∂ℓ/∂a` and the
[rate score](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/rate-score.md) `∂ℓ/∂b` both vanish
at `(a, b̂(a))`.
