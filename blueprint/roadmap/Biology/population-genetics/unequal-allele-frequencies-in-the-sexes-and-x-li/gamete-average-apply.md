# Averaging the two gamete laws, for arbitrary allele types

Let
`coin : PMF Bool` be a fair coin. Form ordered offspring genotypes from
independent female and male gamete laws `pf` and `pm`, then transmit one of
the two coordinates of an ordered genotype using `coin`. For every allele
`a` in an arbitrary type `A` (no finiteness assumption), the resulting mass
at `a` is the average `2⁻¹ * pf a + 2⁻¹ * pm a`. This is the PMF-level form
of the two-sex allele-frequency average.
