# Rao's score test with an estimated information, vector parameter

Under the hypotheses
of `VectorInference.tendstoInDistribution_scoreStatistic`, let `Î n` be any a.e.-measurable
estimators with `Î n → I(θ₀)` in probability (operator norm), for example the observed
information `Ĵₙ(θ₀)` (`tendstoInMeasure_observedInformation`). Then
`⟪Î n⁻¹ Sₙ, Sₙ⟫ → χ²_d`, `Sₙ = n^{-1/2} ∑_{i<n} score p θ₀ (X i)`, `d = dim E ≥ 1`. The inverse
is `Ring.inverse`, which is `0` at singular `Î n ω`; that event has probability tending to `0`.

## Sources

- Rao (1948); van der Vaart (1998), ch. 16.
