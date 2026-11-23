# `Var(ĥ²) → 0` for LD-score regression

For the statistics `χ²_j = chiSqStrat` of the
merged LD-score model with stratification, along designs with `M → ∞`, `N ≥ κ M`, LD-score
spread `S_ℓℓ ≥ c M`, and the LD-block model (block size at most `K`, `Var(χ²_j) ≤ V`), the
LD-score regression estimator `ĥ² = b̂ · M / N` (T147's `h2Hat`, passed in through `hest`)
satisfies `evariance ĥ² → 0`. This is the `hvar` hypothesis of T147's consistency theorem
`tendstoInMeasure_h2Hat`.
