# Independent statistics give PRDS p-values

Let `μ` be a probability measure on `Ω` and `(T, G)` a
[tail-calibrated family](is-tail-calibrated-family.md) of `m` tests with true nulls `H0`. If the
statistics `T 0, …, T (m - 1)` are mutually independent under `μ`, then the
[p-values](tail-pvalue.md) `p_i = G i ∘ T i` are positively regression dependent on every subset
`H0'` of `{0, …, m - 1}`: for every `i ∈ H0'` and every measurable set `D ⊆ ℝ^m` closed under
increasing coordinates, the conditional probability `x ↦ μ(p ∈ D | p_i = x)` has a nondecreasing
version.
