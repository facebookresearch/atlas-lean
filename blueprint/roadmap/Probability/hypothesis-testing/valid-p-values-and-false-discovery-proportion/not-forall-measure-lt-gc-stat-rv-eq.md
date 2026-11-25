# The λ̂-corrected statistic is never exactly χ²₁-calibrated

Let `P` be any measure on a measurable space `Ω`, `Z_0, …, Z_{m-1}` any real functions on `Ω`
(random scores) and `j` a gene. The [corrected statistic](gc-stat-rv.md) `T_j = Z_j² / λ̂` is not
exactly calibrated against `χ²₁`: the equality `P(T_j > c) = P(χ²₁ > c)` fails for some real `c`,
namely at `c = m`, where the left side is `0` and the [`χ²₁` tail](../../../Biology/statistical-genetics/association-tests/genomic-control/chi-sq-one-tail.md) is positive.
This holds whatever the law of the scores, in particular in the [common-inflation
model](../../../Biology/statistical-genetics/association-tests/genomic-control/common-inflation-model.md), where dividing by the true `λ` is exactly calibrated.
