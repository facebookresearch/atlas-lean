# Expected allelic richness of a founder sample

For real allele frequencies `p` on a finite set `A` of alleles and a sample size `k`, the expected
richness is `∑_s (∏_{j=1}^k p(s_j)) · |{s_1, …, s_k}|`, the sum over the ordered samples
`s ∈ A^k` of the [sample weight](sample-weight.md) times the number of distinct
[retained alleles](retained-alleles.md). For admissible frequencies (`p ≥ 0` and
`∑_a p(a) = 1`) the weights are probabilities and it is the expected number of distinct alleles
retained in a founder sample of `k` gene copies drawn independently with replacement: the allelic
richness `a_g` of Kalinowski (2004) at `g = k`, for with-replacement (binomial) sampling. For other
frequencies it is the same weighted sum, which need not be an expectation.
