# Absence weight of an allele in founder sampling

For real allele frequencies `p` on a finite set `A` of alleles, a sample size `k` and an allele
`i`, the absence weight of `i` is the total [sample weight](sample-weight.md)
`∑_s ∏_{j=1}^k p(s_j)` of the ordered samples `s ∈ A^k` that do not contain `i` (`i` is not among
the [retained alleles](retained-alleles.md) of `s`). For admissible frequencies (`p ≥ 0` and
`∑_a p(a) = 1`) it is the probability that allele `i` is lost in a founder sample of `k` gene
copies drawn independently with replacement.
