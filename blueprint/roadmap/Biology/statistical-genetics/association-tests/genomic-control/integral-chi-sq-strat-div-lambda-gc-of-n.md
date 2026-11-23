# Common stratification, h² = 0: every marker is calibrated in mean

Let `μ` be a probability measure and consider an
[LD-score model](../../ld-score-regression/model.md) on `μ` with no polygenic signal
(`h² = 0`), `N ≥ 1` individuals and `M ≥ 1` markers, whose marker effects and noise terms all
have mean zero, and a [standardized](../../ld-score-regression/is-standardized.md) real `N × M`
genotype matrix `X`. Let `s ∈ ℝ` and `c ∈ ℝ^N`, and suppose that the stratification term is
common to all markers: `s² r_j² = a` for every marker `j`, where
`r_j = (1 / N) ∑_i X_ij c_i`. Then

`λ_GC = 1 + N a` and `𝔼[χ²_j] / λ_GC = 1` for every marker `j`,

where `λ_GC` is the [population genomic-control factor](lambda-gc.md) and
`𝔼[χ²_j] = ∫ χ²_j dμ` is the expected
[association statistic under stratification](../../ld-score-regression/chi-sq-strat.md) of
marker `j`: genomic control is calibrated in mean.
