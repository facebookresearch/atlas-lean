# The λ̂ family is tail-calibrated iff its null tails lie below χ²₁

Let `P` be any measure on a measurable space `Ω`, let the random scores `Z_0, …, Z_{m-1}` be
measurable and let `H0` be a set of genes (the true nulls). Give every gene the [real-valued `χ²₁`
tail](chi-sq-one-tail-real.md) `G(s) = P(χ²₁ > s)` as reference tail. The [corrected
statistics](gc-stat-rv.md) `T_j` form a [tail-calibrated
family](../benjamini-hochberg-procedure/is-tail-calibrated-family.md) with true
nulls `H0` (measurable statistics, nonincreasing reference tails, and `P(T_i ≥ s) ≤ G(s)` for every
`i ∈ H0` and every real `s`) if and only if

`P(T_i ≥ s) ≤ P(χ²₁ > s)` for every `i ∈ H0` and every real `s`.

The first two conditions always hold here, so calibration of the estimated-factor family is an
assumption on the null tails of the `T_i` themselves. It does not follow from the [common-inflation
model](../../../Biology/statistical-genetics/association-tests/genomic-control/common-inflation-model.md): with two independent `𝒩(0, λ)` null scores it [fails for every
set of true nulls containing gene `0`](not-is-tail-calibrated-family-gc-stat-rv-2.md). Under the
global null (`H0` the set of all genes), for a probability measure `P`, `m ≥ 1` and scores that are
almost surely not all zero, it [never holds](not-is-tail-calibrated-family-gc-stat-rv.md): for such
scores it can hold only if `H0` leaves out some gene.
