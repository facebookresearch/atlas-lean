# Null p-values of a tail-calibrated family are valid

For a [tail-calibrated family](is-tail-calibrated-family.md) of `m` tests under a measure `μ` with
true nulls `H0`, and every `i ∈ H0`, the [p-value](tail-pvalue.md) `ω ↦ G i (T i ω)` is
[valid](../valid-p-values-and-false-discovery-proportion/is-valid-pvalue.md)
under `μ`: `μ{ω : G i (T i ω) ≤ t} ≤ t` for every `t ∈ [0, 1]`, by
[validity from a dominating reference tail](is-valid-pvalue-of-tail-le.md).
