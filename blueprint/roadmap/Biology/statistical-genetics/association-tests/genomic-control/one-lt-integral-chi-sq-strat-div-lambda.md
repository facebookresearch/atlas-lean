# Common stratification, h² ≠ 0: under-correction above mean LD score

Let `μ` be a probability measure and consider an
[LD-score model](../../ld-score-regression/model.md) on `μ` with polygenic signal (`h² ≠ 0`),
`N ≥ 1` individuals and `M ≥ 1` markers, whose marker effects and noise terms all have mean
zero, and a [standardized](../../ld-score-regression/is-standardized.md) real `N × M` genotype
matrix `X`. Let `s ∈ ℝ` and `c ∈ ℝ^N`, and suppose that the stratification term is common to
all markers: `s² r_j² = a` for every marker `j`, where `r_j = (1 / N) ∑_i X_ij c_i`. Then
every marker `j` whose LD score is above the mean, `ℓ_j > ℓ̄`, is under-corrected in mean:

`𝔼[χ²_j] / λ_GC > 1`,

where `𝔼[χ²_j] = ∫ χ²_j dμ` is the expected
[association statistic under stratification](../../ld-score-regression/chi-sq-strat.md) of
marker `j`, `λ_GC` the [population genomic-control factor](lambda-gc.md), `ℓ_j` the
[LD score](../../ld-score-regression/ld-score.md) of marker `j` and `ℓ̄` the
[mean LD score](../../ld-score-regression/mean-ldscore.md).
