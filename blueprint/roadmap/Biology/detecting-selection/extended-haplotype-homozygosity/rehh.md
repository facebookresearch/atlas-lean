# Relative extended haplotype homozygosity (REHH)

Relative extended haplotype homozygosity: the core-labelled EHH of the core-allele
carriers `C` divided by the core-labelled EHH of the pooled set `D` of haplotypes carrying
the other core alleles. The denominator counts only pairs sharing a core allele, so
cross-core pairs never inflate it. This is the statistic of the long-range haplotype test
(Sabeti et al. 2002). It is a junk value `0` when the denominator vanishes;
`one_lt_rehh_iff` assumes a positive denominator.
