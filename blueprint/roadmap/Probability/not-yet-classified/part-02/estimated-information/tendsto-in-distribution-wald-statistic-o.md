# Wald's test with an estimated information, vector parameter

Under the hypotheses of
`VectorInference.tendstoInDistribution_waldStatistic`, let `Î n` be any a.e.-measurable
operator-valued estimators with `Î n → I(θ₀)` in probability (operator norm), for example the
observed information `Ĵₙ(θhat n)` (`tendstoInMeasure_observedInformation_of_tendstoInMeasure`),
`Ĵₙ(θ₀)`, or `I(θhat n)` when `I` is continuous at `θ₀`
(`tendstoInMeasure_fisherInformation_comp`). Then the Wald statistic
`n ⟪Î n (θhat n - θ₀), θhat n - θ₀⟫` converges in distribution to `χ²_d`, `d = dim E ≥ 1`.

## Sources

- Wald (1943); van der Vaart (1998), ch. 16.
