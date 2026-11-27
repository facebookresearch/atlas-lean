# Genomic-control p-values are valid in the common-inflation model

Consider a [common-inflation model](common-inflation-model.md) on a measure `P`, with inflation
factor `λ > 0` and null scores `Z_j`, each with law `𝒩(0, λ)` under `P`. For every marker `j`,
the [genomic-control p-value](gc-pvalue.md) `p_j = G(Z_j² / λ)`, where `G(y) = P(χ²₁ > y)` is
the [`χ²₁` tail](chi-sq-one-tail.md) read as a real number, is a
[valid p-value](../../../../Probability/hypothesis-testing/valid-p-values-and-false-discovery-proportion/is-valid-pvalue.md)
under `P`:

`P(p_j ≤ t) ≤ t` for every `t ∈ [0, 1]`.
