# The coalescent with separate sexes

For a diploid population with $N_m$ breeding males and $N_f$ breeding females, $N = N_m + N_f$, the genealogy of autosomal genes is a structured Wright–Fisher model (Nordborg 2001; Ramachandran, Rosenberg, Feldman and Wakeley 2008): a lineage in either sex comes from a male or a female parent with probability $1/2$ each, and states with two distinct lineages in one individual are instantaneous on the coalescent time scale, so the dependence they introduce does not affect the limit. Two lineages in different individuals coalesce in the previous generation if and only if they come from the same sex, the same individual of that sex and the same gene of that individual, with probability

$$\frac14\cdot\frac1{N_m}\cdot\frac12 + \frac14\cdot\frac1{N_f}\cdot\frac12 = \frac{N_m + N_f}{8N_mN_f}$$

(the two terms $1/(8N_m)$ and $1/(8N_f)$ are the inheritance factors of the coalescence entries of the single-generation transition matrix (1) of Ramachandran et al.). Hence, with $c_m = N_m/N$ and $c_f = N_f/N$ fixed, pairs coalesce at rate $(4c_mc_f)^{-1}$ on the $2N$-generation scale, and the genealogy of a sample is [Kingman's coalescent](../partition-valued-kingman-coalescent/partition-rate.md) when time is measured in units of $2N_e = 8N_mN_f/(N_m + N_f)$ generations, which reduces to $2N$ when $N_m = N_f$.

Ramachandran et al. write the transition matrix as $\mathbf P = \mathbf D + \mathbf B/N + \mathbf E_N$ (their eq. (3)), with $\mathbf D$ the fast movement of lineages between the sexes by Mendelian inheritance, and apply Möhle's (1998) separation-of-time-scales theorem. In their island model the within-deme pair coalescence rate is $1/(8r(1 - r))$ per $N$ generations, with $r = N_f/N$ the female fraction (eq. (7)), which is $(4c_mc_f)^{-1}$ per $2N$ generations; the expected within-deme coalescence time is $8Dr(1 - r)$ units of $N$ generations for $D$ demes (eq. (8)). Their Discussion identifies these rates as half the reciprocal of the variance effective size $N_e = 4N_mN_f/(N_m + N_f)$.

## Depends on

- [Rate matrix of Kingman's partition-valued coalescent](../partition-valued-kingman-coalescent/partition-rate.md)
- [Effective population size with separate sexes](../../../Biology/population-genetics/effective-population-size/effective-size-with-separate-sexes.md)

## Expansion

1. The two-sex model as a structured Wright–Fisher model with two patches of sizes $2N_m$ and $2N_f$, each divided into individuals.
2. The pair coalescence probability above and the instantaneous within-individual states.
3. The limit to Kingman's coalescent on the $2N_e$-generation scale, by Möhle's separation-of-time-scales theorem (Ramachandran et al., eqs. (3) and (7)).
4. Other inheritance modes, each with its own clock: X-linked genes, transmitted by females to both sexes and by males to daughters only (Ramachandran et al. treat them with matrix (2) and eq. (6), with $N_e = 9N_mN_f/(4N_m + 2N_f)$ in their Discussion), and maternally inherited mitochondrial genes; their pair coalescence probabilities as separate statements.

## Sources

- S. Ramachandran, N. A. Rosenberg, M. W. Feldman and J. Wakeley, Population differentiation and migration: coalescence times in a two-sex island model for autosomal and X-linked loci, Theor. Popul. Biol. 74 (2008), 291–301, matrix (1), eqs. (3), (7) and (8), and Discussion. Open copy at PMC: <https://pmc.ncbi.nlm.nih.gov/articles/PMC2630000/>. <https://doi.org/10.1016/j.tpb.2008.08.003>
- M. Nordborg, Coalescent theory, in D. J. Balding, M. Bishop and C. Cannings (eds.), *Handbook of Statistical Genetics*, Wiley, Chichester, 2001, pp. 179–212 (general reference for the two-sex model).
