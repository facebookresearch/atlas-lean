# Two-gene λ̂ p-values are not PRDS when T₀ falls on both sides of 1

Let `P` be a nonzero finite measure on a measurable space `Ω` and let `Z_0, Z_1` be measurable
random scores of two genes that are almost surely not both zero. Let `T_0, T_1` be their [corrected
statistics](gc-stat-rv.md) and `p_j = G(T_j)` their `χ²₁` p-values (the [tail
p-values](../benjamini-hochberg-procedure/tail-pvalue.md) of the family), where
`G(t)`, the probability that a `χ²₁` variable exceeds `t`, is the
[real-valued `χ²₁` tail](chi-sq-one-tail-real.md). If both events
`{T_0 ≥ 1}` and `{T_0 < 1}` have positive measure, then the p-values are not PRDS on any set `H0` of
true nulls containing gene `0`. Here PRDS on `H0` means: for every `i ∈ H0` and every measurable
increasing set `D ⊆ ℝ²`, the conditional probability that `(p_0, p_1) ∈ D` given `p_i = x` has a
nondecreasing version in `x`. No independence, Gaussianity or other assumption on the scores is
involved: almost surely `T_1 = 2 - T_0` ([two-gene sum](gc-stat-two-add.md)), which makes `p_1` a
decreasing function of `p_0`.
