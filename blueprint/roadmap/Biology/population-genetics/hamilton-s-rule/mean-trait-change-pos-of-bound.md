# Robust Hamilton's rule for an increase of the mean trait

On a finite set of individuals, let the fitnesses be [additive](additive-fitness.md),
`w i = α + b * y i - c * z i + e i`, with positive mean `𝔼 i, w i > 0`, and let the trait have
nonzero variance, `Var(z) ≠ 0`. If, for a real `ε`, the residual and transmission terms satisfy
`|Cov(e, z) + E[w (z' - z)]| ≤ ε Var(z)` and `r b - c > ε`, then the mean trait increases,
`Δz̄ > 0`. Here `Δz̄` is the [change in mean trait](mean-trait-change.md), `Cov` and `Var` are the
[population covariance and variance](pop-cov.md), `r = Cov(y, z) / Var(z)` is the
[regression relatedness](relatedness.md) and `E[w (z' - z)]` is the
[transmission term](transmission.md).
