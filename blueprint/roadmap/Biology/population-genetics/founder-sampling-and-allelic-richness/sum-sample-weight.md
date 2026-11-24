# Founder sample weights sum to one when the frequencies do

For real allele frequencies `p` on a finite set `A` of alleles with `∑_a p(a) = 1`, of any sign,
and every sample size `k`, the [sample weights](sample-weight.md) of all ordered samples sum to
`1`: `∑_{s ∈ A^k} ∏_{j=1}^k p(s_j) = 1`.
