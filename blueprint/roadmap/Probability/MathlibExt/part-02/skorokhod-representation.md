---
article_id: af_7659284c51d4ab262380b49c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Probability.SkorokhodRepresentationWanted.skorokhod_representation
---

# Skorokhod Representation

If `μₙ : ℕ → ProbabilityMeasure X` converges weakly to `μ₀` on a Polish space `X`, then there
exist measurable `Yₙ, Y₀ : ℝ → X` with `(volume.restrict (Icc 0 1)).map Yₙ = μₙ`,
`(volume.restrict (Icc 0 1)).map Y₀ = μ₀` and `Yₙ → Y₀` a.s. for `volume.restrict (Icc 0 1)`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Cdf Quantile](quantile/cdf-quantile.md)
- [Cdf Quantile le iff](quantile/cdf-quantile-le-iff.md)
- [Cdf Quantile mono On](quantile/cdf-quantile-mono-on.md)
- [Map cdf Quantile restrict Icc](quantile/map-cdf-quantile-restrict-icc.md)
- [Measurable cdf Quantile](quantile/measurable-cdf-quantile.md)

## Sources

- [MathlibExt, MathlibExt.Probability.SkorokhodRepresentation](../../../../sources/v2/MathlibExt.md)
- A. V. Skorokhod, Limit theorems for stochastic processes, Theory Probab. Appl. 1 (1956) 261–290; textbook in Billingsley, Convergence of Probability Measures, 2nd ed., Foundations of Modern Probability (Icc 0 1)` source, `Icc` Lebesgue base; standard version on `[0, 1]` with Lebesgue.
