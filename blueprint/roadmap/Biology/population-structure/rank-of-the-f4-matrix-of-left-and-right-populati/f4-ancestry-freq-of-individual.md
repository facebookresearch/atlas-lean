# f4 statistics of an individual are combinations of ancestral ones

Let `K` be a finite set, `μ` a measure on the set `J` of loci, and `Q : I → K → ℝ`, `F : K → J → ℝ`
real arrays with `∑ k, Q i k = 1` for every individual `i` (no sign condition), such that every
frequency of the [global-ancestry family](ancestry-freq-of.md) of `Q` and `F` is square integrable
for `μ`. Then for every individual `i` and all members `X`, `Y`, `Z` of the family,
`f4(i, X; Y, Z) = ∑ k, Q i k * f4(k, X; Y, Z)`, where `k` runs over the ancestral populations and
`f4` is the [f4 statistic](../patterson-s-f-statistics/f4.md) over loci.
