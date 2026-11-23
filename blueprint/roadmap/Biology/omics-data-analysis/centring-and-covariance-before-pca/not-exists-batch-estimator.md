# Batch effect nonidentifiable

In a confounded design (with at least one feature) no
function of the centered sample covariance recovers the batch effect `β`: "all batch"
`(β, δ) = (a, 0)` and "all biology" `(β, δ) = (0, a)` give the same `S`. Compare
`MathlibExt.Biology.Omics.Pseudobulk.not_identifiable_of_confounded`: the scalar cell-level
hierarchical model (donor-level covariates), for the condition effect `τ` and the full data
law.
