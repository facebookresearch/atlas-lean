# Admixture-model rank bound for the f4 matrix over finitely many loci

Let the set `J` of SNPs be finite, with every subset measurable, and let `μ` be a finite measure on
`J` (for example the counting measure). Let `θ = (Q, F)` be
[parameters of the admixture model](../admixture-model-and-the-frappe-em-algorithm/params.md) with
individuals `0, …, n`, SNPs `J` and ancestral populations `0, …, k` (`Q i l > 0`, `∑ l, Q i l = 1`
for every `i`, and `0 < F l j < 1`). Then for all right populations `R 0, …, R r` of the
[admixture-model family](ancestry-freq.md), the
[qpWave matrix](../abba-baba-test-and-f-statistic-estimators/f4-matrix.md) with the individuals as
left populations and individual `0` as their reference, with entries `f4(i, 0; R j, R 0)` for
`1 ≤ i ≤ n` and `1 ≤ j ≤ r`, has rank at most `k`. On such a `J` every frequency is square
integrable.
