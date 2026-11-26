# The coalescent with separate sexes

For a diploid population with $N_m$ breeding males and $N_f$ breeding females, $N = N_m + N_f$, Nordborg (2001, section "Males and females") treats the genealogy of autosomal genes as a structured Wright–Fisher model: a lineage in either sex comes from a male or a female parent with probability $1/2$ each, and states with two distinct lineages in one individual are instantaneous on the coalescent time scale, so the dependence they introduce does not affect the limit. Two lineages in different individuals coalesce in the previous generation if and only if they come from the same sex, the same individual of that sex and the same gene of that individual, with probability

$$\frac14\cdot\frac1{N_m}\cdot\frac12 + \frac14\cdot\frac1{N_f}\cdot\frac12 = \frac{N_m + N_f}{8N_mN_f}$$

(equation (15)). Hence, with $c_m = N_m/N$ and $c_f = N_f/N$ fixed, pairs coalesce at rate $(4c_mc_f)^{-1}$ on the $2N$-generation scale, and the genealogy of a sample is Kingman's coalescent when time is measured in units of $2N_e = 8N_mN_f/(N_m + N_f)$ generations (equation (16)), which reduces to $2N$ when $N_m = N_f$.

## Depends on

- [Effective population size with separate sexes](../../../Biology/population-genetics/effective-population-size/effective-size-with-separate-sexes.md)

## Expansion

1. The two-sex model as a structured Wright–Fisher model with two patches of sizes $2N_m$ and $2N_f$, each divided into individuals.
2. The pair coalescence probability (15) and the instantaneous within-individual states.
3. The limit to Kingman's coalescent on the $2N_e$-generation scale.
4. Other inheritance modes, each with its own clock: X-linked genes, transmitted by females to both sexes and by males to daughters only, and maternally inherited mitochondrial genes; their pair coalescence probabilities as separate statements.

## Sources

- M. Nordborg, Coalescent theory, in *Handbook of Statistical Genetics*, Wiley, 2001 (preprint of March 2000), section "Males and females", equations (15) and (16).
