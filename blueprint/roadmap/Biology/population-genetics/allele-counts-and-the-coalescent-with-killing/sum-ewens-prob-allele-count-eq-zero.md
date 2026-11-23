# Configurations not totalling the sample size get zero Ewens weight

Let `θ` be real and let `a = (a_1, a_2, …)` be natural numbers with `∑_{j=1}^n j a_j ≠ n`. Since
the configuration of every allelic partition of `n` satisfies
[`∑_{j=1}^n j a_j = n`](sum-mul-allele-count.md), no partition of `n` has a configuration agreeing
with `a` at `j = 1, …, n`, and the sum of the
[Ewens sampling formula](../ewens-sampling-formula-and-the-chinese-restauran/ewens-prob.md) over
such partitions is `0`. For `θ > 0` this says that the sample has configuration `a` with
probability `0`.
