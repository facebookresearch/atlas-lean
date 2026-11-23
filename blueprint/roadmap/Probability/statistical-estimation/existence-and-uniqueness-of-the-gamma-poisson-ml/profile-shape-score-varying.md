# Profile shape score along the rate root

For a finite family of counts `k₁, …, kₙ`, real size factors `s₁, …, sₙ` and a real shape `a`, the
profile shape score is `∂ℓ/∂a (a, b̂(a))`: the
[shape score](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/shape-score.md)
`∑ᵢ (∑_{j<kᵢ} 1 / (a + j) + log b - log (b + sᵢ))` of the
[log marginal likelihood](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/log-marginal-lik.md)
`ℓ` at `b = b̂(a)`, the [rate root](rate-root.md).

For positive size factors, `n ≥ 1` and at least one positive count, its zeros in `(0, ∞)` are
exactly the shapes of the solutions in `(0, ∞)²` of the joint score equations: `(a, b)` with `a > 0`
and `b > 0` is such a solution if and only if `a` is a zero and `b = b̂(a)`
([the joint score equations reduce to the profile](score-eq-zero-iff-rate-root.md)).

Where there is no positive rate root, `b̂(a) = 0` and the value is
`∑ᵢ (∑_{j<kᵢ} 1 / (a + j) - log sᵢ)`, with the conventions `log 0 = 0`, `log x = log |x|` and
`1 / 0 = 0`. For example, for `a > 0`, positive size factors and all counts `0` it is `-∑ᵢ log sᵢ`,
which vanishes when `∏ᵢ sᵢ = 1`. At a common size factor `σ > 0` with
[sample mean](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/count-mean.md) `M > 0` and
`a > 0`, it is the
[profile shape score](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/profile-shape-score.md)
`∑ᵢ ∑_{j<kᵢ} 1 / (a + j) - n (log (a + M) - log a)`
([closed form at a common size factor](profile-shape-score-varying-const.md)).
