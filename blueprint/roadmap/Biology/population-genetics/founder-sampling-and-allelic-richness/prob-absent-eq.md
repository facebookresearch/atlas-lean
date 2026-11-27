# Allele loss under founder sampling

For real allele frequencies `p` on a finite set of alleles with `∑_a p(a) = 1`, of any sign, every
sample size `k` and every allele `i`, the [absence weight](prob-absent.md) of `i` is
`(1 - p(i)) ^ k`. For admissible frequencies (also `p ≥ 0`) this is the probability that allele
`i` is absent from a founder sample of `k` gene copies drawn independently with replacement.
