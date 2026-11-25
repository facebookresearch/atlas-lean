# Global-ancestry frequencies of individuals and ancestral populations

Let `I` be a set of individuals, `J` a set of loci and `K` a finite set of ancestral populations,
and let `Q : I → K → ℝ` (ancestry proportions) and `F : K → J → ℝ` (ancestral allele frequencies) be
real arrays. The global-ancestry frequency family is indexed by the individuals and the ancestral
populations together: individual `i` has frequency `∑ k, Q i k * F k j` at locus `j`, and ancestral
population `k` has frequency `F k j`. With the loci as the sample space, these are allele
frequencies for f-statistics. The definition takes `Q` and `F` without any sign, sum or bound
condition; in use, each `Q i` is a vector of nonnegative ancestry proportions summing to `1` and
`0 ≤ F k j ≤ 1`.
