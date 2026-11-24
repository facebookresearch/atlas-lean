# Hamilton's rule for a decrease of the mean trait

On a finite set of individuals, let the fitnesses be [additive](additive-fitness.md),
`w i = α + b * y i - c * z i + e i`, with positive mean `𝔼 i, w i > 0`; let the trait have
nonzero variance, `Var(z) ≠ 0`; let the residual be uncorrelated with the trait, `Cov(e, z) = 0`;
and let the transmission term vanish, `E[w (z' - z)] = 0` (for instance with faithful
transmission, `z' = z`). Then the mean trait decreases, `Δz̄ < 0`, if and only if `r b < c`. Here
`Δz̄` is the [change in mean trait](mean-trait-change.md), `Cov` and `Var` are the
[population covariance and variance](pop-cov.md), `r = Cov(y, z) / Var(z)` is the
[regression relatedness](relatedness.md) and `E[w (z' - z)]` is the
[transmission term](transmission.md).
