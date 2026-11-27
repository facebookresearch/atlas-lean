# Individual frequencies are combinations of the ancestral frequencies

Let `K` be a finite set and `Q : I → K → ℝ`, `F : K → J → ℝ` arbitrary real arrays. In the
[global-ancestry frequency family](ancestry-freq-of.md) of `Q` and `F`, the frequency of individual
`i` at locus `j` is `∑ k, Q i k * F k j`, the combination with coefficients `Q i k` of the
frequencies `F k j` of the ancestral populations `k`. When the coefficients are nonnegative and sum
to `1`, the individual is an exact mixture of the ancestral populations, with no private drift.
