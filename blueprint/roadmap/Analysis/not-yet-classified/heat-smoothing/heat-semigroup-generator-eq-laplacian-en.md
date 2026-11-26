# Heat semigroup generator eq laplacian ennreal

The `L^p` heat-semigroup generator equals the Laplacian on compactly supported `C²` data:
for finite `p ≥ 1`, the right-hand difference quotient `(heatConvolution n φ t - φ) / t`
converges to `Δφ` in `L^p` as `t → 0⁺`, i.e. `‖heatConvolution n φ t - φ - t * Δφ‖_p / t → 0`.
This is stated directly with `eLpNorm` in `ENNReal` (the `ENNReal`-valued form is the genuine
`L^p` statement: `ENNReal.toReal` sends `⊤` to `0`, so a real-valued limit alone could report
convergence even when the remainder is not in `L^p`).
