# For positive definite V the null burden variance is nonnegative

Let `V` be a positive definite real `n × n` matrix and `X` a real `n × q` covariate matrix with
`Xᵀ V⁻¹ X` invertible. For every real `n × m` genotype matrix `G` and variant weights `a ∈ ℝᵐ`,

`Cᵀ P C ≥ 0`, with `C = G a`,

where `P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is the
[null projection](../../../Biology/statistical-genetics/association-tests/skat-variance-component-test/proj-p.md). Indeed `P` is symmetric and
`P V P = P`, so `Cᵀ P C = (P C)ᵀ V (P C) ≥ 0`. Under these hypotheses `Cᵀ P C` is the
[null variance of the burden score](map-burden-score-null.md).
