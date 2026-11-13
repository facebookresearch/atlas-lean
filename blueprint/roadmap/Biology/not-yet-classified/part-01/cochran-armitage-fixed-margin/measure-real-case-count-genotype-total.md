# Conditional null law of the fixed-margin case–control table

In the product-binomial
design, `R` cases (subjects `0, …, R - 1`) and `S` controls (subjects `R, …, R + S - 1`) are
sampled independently, the cases with genotype law `πcase` and the controls with genotype law
`πctrl`. Under the null `πcase = πctrl`, conditional on the genotype margin `n` (the class totals
over all `R + S` subjects), the case counts `r` follow the multivariate hypergeometric law
`∏ᵢ C(nᵢ, rᵢ) / C(R + S, R)`, which does not depend on the common genotype law.

The conditional probability is stated without division:
`P(case counts = r, margin = n) = H(r ∣ n) · P(margin = n)`, so it also holds for margins of
probability zero.
