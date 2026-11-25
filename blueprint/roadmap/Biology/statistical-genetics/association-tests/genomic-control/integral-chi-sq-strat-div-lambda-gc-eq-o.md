# Common stratification, h² ≠ 0: calibration exactly at mean LD score

Let `μ` be a probability measure and consider an
[LD-score model](../../ld-score-regression/model.md) on `μ` with polygenic signal (`h² ≠ 0`),
`N ≥ 1` individuals and `M ≥ 1` markers, whose marker effects and noise terms all have mean
zero, and a [standardized](../../ld-score-regression/is-standardized.md) real `N × M` genotype
matrix `X`. Let `s ∈ ℝ` and `c ∈ ℝ^N`, and suppose that the stratification term is common to
all markers: `s² r_j² = a` for every marker `j`, where `r_j = (1 / N) ∑_i X_ij c_i`. Then, for
every marker `j`,

`𝔼[χ²_j] / λ_GC = 1` if and only if `ℓ_j = ℓ̄`,

where `𝔼[χ²_j] = ∫ χ²_j dμ` is the expected
[association statistic under stratification](../../ld-score-regression/chi-sq-strat.md) of
marker `j`, `λ_GC` the [population genomic-control factor](lambda-gc.md), `ℓ_j` the
[LD score](../../ld-score-regression/ld-score.md) of marker `j` and `ℓ̄` the
[mean LD score](../../ld-score-regression/mean-ldscore.md): genomic control calibrates a marker
in mean exactly when its LD score equals the mean LD score. With `h² ≠ 0` every marker effect
has second moment `h² / M ≠ 0`, so no marker is null, and calibration in mean concerns the
expected statistic, not type I error.
