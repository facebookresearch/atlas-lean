# At empirical frequencies the criterion is the average log-likelihood

Let `σ` be a finite set, `law` any map from a set `Θ` to the functions `σ → ℝ` and `X i : Ω → σ`
columns. The [log-likelihood criterion](log-lik.md) at the
[empirical site-pattern frequencies](../consistency-of-minimum-distance-gtr-estimators/empirical-freq.md)
`p̂ₙ(ω)` of the first `n` columns is the average log-likelihood of those columns:
`L(p̂ₙ(ω), θ) = n⁻¹ · ∑_{i < n} log (law θ (X i ω))` for every `θ`, `n` and `ω`. At `n = 0` both
sides are `0`, with the convention `0⁻¹ = 0`.
