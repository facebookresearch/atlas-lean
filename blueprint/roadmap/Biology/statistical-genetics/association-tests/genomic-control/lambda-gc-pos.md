# The population genomic-control factor is positive

Let `μ` be a probability measure and consider an
[LD-score model](../../ld-score-regression/model.md) on `μ` with heritability `h² ≠ 0`,
`N ≥ 1` individuals and `M ≥ 1` markers, whose marker effects and noise terms all have mean
zero, and a [standardized](../../ld-score-regression/is-standardized.md) real `N × M` genotype
matrix `X`. Let `s ∈ ℝ` and `c ∈ ℝ^N`, and suppose that the stratification term is common to
all markers: `s² r_j² = a` for every marker `j`, where `r_j = (1 / N) ∑_i X_ij c_i` (so
`a ≥ 0`). Then the [population genomic-control factor](lambda-gc.md) is positive: `λ_GC > 0`.
