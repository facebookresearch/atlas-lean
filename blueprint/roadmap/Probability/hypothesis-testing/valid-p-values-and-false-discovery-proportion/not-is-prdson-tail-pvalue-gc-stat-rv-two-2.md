# Two independent null genes: the λ̂ p-values are not PRDS

Let `P` be a probability measure and let the two scores `Z_0, Z_1` of the [common-inflation
model](../../../Biology/statistical-genetics/association-tests/genomic-control/common-inflation-model.md), each with law `𝒩(0, λ)` under `P` for one `λ > 0`, be measurable
and independent. Then the `χ²₁` p-values `p_j = G(T_j)` of the [corrected
statistics](gc-stat-rv.md), with `G` the [real-valued `χ²₁` tail](chi-sq-one-tail-real.md), are not
PRDS on any set `H0` of true nulls containing gene `0` (PRDS as defined in the [general two-gene
criterion](not-is-prdson-tail-pvalue-gc-stat-rv-two.md)). The conditions of that criterion hold: the
scores are [almost surely not both zero](ae-sum-sq-ne-zero.md), and `{T_0 ≥ 1}` and `{T_0 < 1}` each
have probability at least `1/2`.
