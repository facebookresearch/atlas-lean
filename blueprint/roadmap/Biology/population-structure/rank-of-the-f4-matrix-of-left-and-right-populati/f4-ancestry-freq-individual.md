# Admixture-model f4 statistics of an individual mix the ancestral ones

Let `θ = (Q, F)` be
[parameters of the admixture model](../admixture-model-and-the-frappe-em-algorithm/params.md) with
individuals `I`, SNPs `J` and a finite set `K` of ancestral populations (`Q i k > 0`,
`∑ k, Q i k = 1` for every `i`, and `0 < F k j < 1`), and let `μ` be a measure on `J` for which
every frequency of the [admixture-model family](ancestry-freq.md) is square integrable. Then for
every individual `i` and all members `X`, `Y`, `Z` of the family,
`f4(i, X; Y, Z) = ∑ k, Q i k * f4(k, X; Y, Z)`, where `f4` is the
[f4 statistic](../patterson-s-f-statistics/f4.md) over SNPs. Of the parameter constraints, only the
row sums `∑ k, Q i k = 1` are used, not the positivity conditions; square integrability is still
assumed.
