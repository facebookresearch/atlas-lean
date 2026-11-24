# Unequal stratification, h² = 0: no single λ calibrates both markers

Let `μ` be a probability measure and consider an
[LD-score model](../../ld-score-regression/model.md) on `μ` with no polygenic signal
(`h² = 0`), `N ≥ 1` individuals and `M` markers, whose marker effects and noise terms all have
mean zero, and a [standardized](../../ld-score-regression/is-standardized.md) real `N × M`
genotype matrix `X`. Let `s ∈ ℝ` and `c ∈ ℝ^N`, and let `j` and `k` be two markers whose
stratification terms differ: `s² r_j² ≠ s² r_k²`, where `r_l = (1 / N) ∑_i X_il c_i` for every
marker `l`. Then there is no real number `λ` with

`𝔼[χ²_j] / λ = 1` and `𝔼[χ²_k] / λ = 1`,

where `𝔼[χ²_l] = ∫ χ²_l dμ` is the expected
[association statistic under stratification](../../ld-score-regression/chi-sq-strat.md) of
marker `l`: no single factor calibrates both markers in mean.
