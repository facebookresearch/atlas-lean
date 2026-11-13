# Extended haplotype homozygosity (EHH)

Extended haplotype homozygosity at radius `d` of the haplotype set `C`: the probability
that two distinct haplotypes drawn from `C` without replacement agree at all `d` sites nearest
the core (Sabeti et al. 2002). For `#C ≤ 1` the denominator vanishes and the junk value `0` is
returned; every statement below that needs the probabilistic reading assumes `2 ≤ #C`.
