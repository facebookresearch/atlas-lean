# Cross-population extended haplotype homozygosity (XP-EHH)

The cross-population extended haplotype homozygosity score (Sabeti et al. 2007): the log
ratio of the integrated haplotype homozygosities of the same core region in two populations.
Both arguments must be positive for the score to be meaningful. Outside that domain
`Real.log` is totalized by Mathlib, not by the stated junk value: `Real.log 0 = 0` and
`Real.log (-x) = Real.log x`, so for example `xpehh (-2) 1 = log 2`.
