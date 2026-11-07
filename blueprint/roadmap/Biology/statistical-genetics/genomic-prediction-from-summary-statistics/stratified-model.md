# Stratified LD-score model

The stratified LD-score model (Finucane et al. 2015), at the level of raw second moments:
annotation categories `cat c ⊆ {markers}` (possibly overlapping), per-category contributions
`tau c`, effects with `∫ β k β l = [k = l] ∑_c τ_c [k ∈ cat c]`, noise with
`∫ ε i ε i' = σ²_e [i = i']`, effects orthogonal to noise. The cited model normalizes the
phenotypic variance so that `σ²_e ≈ 1`; the confounding term `N a` is not modeled.
