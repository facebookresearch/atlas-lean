# Bonferroni-adjusted significance level

Bonferroni-adjusted level `α/m`: each of `m` p-values is compared with `α/m`, meaningful for
`m ≥ 1` (at `m = 0` the value is `0`, by the convention `x / 0 = 0`). It is the threshold of the
[Bonferroni procedure](mem-bonferroni-rejections-iff.md), which, for valid p-values and
`α ∈ [0, 1]`,
[controls the family-wise error rate](../../../Probability/hypothesis-testing/bonferroni-correction/measure-bonferroni-familywise-error-le.md)
at level `α`.
