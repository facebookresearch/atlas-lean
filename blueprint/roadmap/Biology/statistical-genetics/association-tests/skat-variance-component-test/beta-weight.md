# Default SKAT variant weight from the Beta(1, 25) density

The default variant weight of Wu et al. (2011) is the polynomial

`w(MAF) = (25 (1 - MAF)²⁴)²`,

defined for every real `MAF`. For a minor-allele frequency `MAF ∈ [0, 1]`, `25 (1 - MAF)²⁴` is the
density of the Beta(1, 25) law at `MAF`, so `√w = Beta(MAF; 1, 25)`; outside `[0, 1]` the polynomial
is not that density, which vanishes there.
