# BH controls the FDR over the causal nulls

Under strong ignorability given `X` of every
endpoint with zero average treatment effect (nothing is assumed about the other endpoints), with
independent p-values calibrated for the observed-data IPW null, the Benjamini–Hochberg procedure at
level `q ∈ [0, 1]` has false discovery rate at most `q |ateNulls| / m`, the false discoveries being
the rejected endpoints with zero average treatment effect. The merged BH theorem
`integral_falseDiscoveryProportion_bhRejections_le_of_isValidPValue` is applied to the causal nulls
via `isValidPValue_of_mem_ateNulls`. No power claim is made.
