# Hamilton's rule as an exact identity for additive fitness

On a finite set of individuals, let the fitnesses be [additive](additive-fitness.md),
`w i = α + b * y i - c * z i + e i`, with nonzero total `∑ i, w i ≠ 0`, and let the trait have
nonzero variance, `Var(z) ≠ 0`. Then for all mean offspring traits `z'`,
`w̄ Δz̄ = Var(z) (r b - c) + Cov(e, z) + E[w (z' - z)]`, and so, with the variance factored out,
`w̄ Δz̄ = Var(z) (r b - c + (Cov(e, z) + E[w (z' - z)]) / Var(z))`, where `w̄ = 𝔼 i, w i` is the
mean fitness, `Δz̄` the [change in mean trait](mean-trait-change.md), `Cov` and `Var` the
[population covariance and variance](pop-cov.md), `r = Cov(y, z) / Var(z)` the
[regression relatedness](relatedness.md) and `E[w (z' - z)]` the
[transmission term](transmission.md).
