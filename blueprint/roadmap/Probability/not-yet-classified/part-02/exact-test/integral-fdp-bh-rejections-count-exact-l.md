# Exact tests of many genes under arbitrary dependence (Benjamini–Yekutieli)

Test `m`
genes with counts `X g` (condition 1, library size `s₁`) and `Y g` (condition 2, library size
`s₂`) by their exact conditional p-values. If each truly null gene `g ∈ H0` has independent
Poisson counts with a common rate `r g` in both conditions, then BH at level `q / H_m` has false
discovery rate at most `q |H0| / m`, however the genes depend on each other. Nothing is assumed
about the non-null genes beyond measurability.
