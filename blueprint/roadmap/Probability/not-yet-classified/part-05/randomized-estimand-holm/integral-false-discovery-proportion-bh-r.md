# BH under PRDS controls the FDR over the causal nulls

Under strong ignorability given `X`
of every endpoint with zero average treatment effect, with measurable p-values calibrated for the
observed-data IPW null and PRDS on the causal nulls (`IsPRDSOn μ p (ateNulls μ Y₀ Y₁)`), the
Benjamini–Hochberg procedure at level `q ∈ [0, 1]` has false discovery rate at most
`q |ateNulls| / m`, the false discoveries being the rejected endpoints with zero average treatment
effect. This generalizes `integral_falseDiscoveryProportion_bhRejections_ateNulls_le`
(independent p-values are PRDS, `isPRDSOn_of_iIndepFun`). No power claim is made.

## Sources

- Benjamini & Yekutieli (2001), Theorem 1.2.
