# Ewens sampling formula as the law of the allele-count configuration

Let `θ` be real and let `a = (a_1, a_2, …)` be natural numbers with `∑_{j=1}^n j a_j = n`. The
sum of the [Ewens sampling formula](../ewens-sampling-formula-and-the-chinese-restauran/ewens-prob.md)
over the allelic partitions `π` of `n` whose [allele-count configuration](allele-count.md) agrees
with `a` at `j = 1, …, n` is the [configuration form](ewens-config-prob.md)
`n! / (θ (θ + 1) ⋯ (θ + n - 1)) · ∏_{j=1}^n (θ / j) ^ {a_j} / a_j!`, where, by the convention
`x / 0 = 0`, the quotient is `0` when its denominator vanishes, that is when `θ = -i` for an
integer `i` with `0 ≤ i < n` (for `n = 0` the products are empty and the value is `1`). For
`θ > 0`, where the Ewens formula is a
[probability distribution on the partitions of `n`](../ewens-sampling-formula-and-the-chinese-restauran/sum-ewens-prob.md),
this is the probability that the configuration of the sample agrees with `a` at `j = 1, …, n`.
