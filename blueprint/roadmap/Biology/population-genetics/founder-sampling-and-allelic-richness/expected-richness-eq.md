# Expected allelic richness under founder sampling

For real allele frequencies `p` on a finite set of alleles with `∑_a p(a) = 1`, of any sign, and
every sample size `k`, the [expected richness](expected-richness.md) is
`∑_i (1 - (1 - p(i)) ^ k)`. For admissible frequencies (also `p ≥ 0`) this is the expected number
of distinct alleles retained in a founder sample of `k` gene copies drawn independently with
replacement: the sum over alleles of the retention probability `1 - Q_i` of Kalinowski (2004),
with the with-replacement [absence probability](prob-absent-eq.md) `Q_i = (1 - p(i)) ^ k`.
