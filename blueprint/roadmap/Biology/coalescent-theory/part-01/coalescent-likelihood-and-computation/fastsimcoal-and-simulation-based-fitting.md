# Multi-population composite likelihoods and conditional maximization in fastsimcoal2

The [simulation-based composite likelihood of the site frequency spectrum](../../expected-site-frequency-spectrum/simulation-based-sfs-composite-likelihood.md) gives the ratio estimator of the expected spectrum over $Z$ simulated genealogies and the composite multinomial likelihood with monomorphic sites, for one population (Excoffier, Dupanloup, Huerta-Sánchez, Sousa and Foll 2013, Methods, Equations 1–3) and for the joint spectrum of two populations (Equation 4). Beyond that, the same authors extend the likelihood to the joint spectrum of more than two populations, collapse rarely observed entries of the spectrum, and for many populations use a product of pairwise composite likelihoods (Equations 5–7). Because the likelihood is estimated by simulation, it is maximized by a conditional maximization (ECM) algorithm, one parameter at a time with Brent's method. For a bottleneck and a split without migration, where the expected spectrum can be computed exactly, the estimated entries scatter symmetrically around the exact values as the number of simulations grows (Figures S14 and S15).

## Depends on

- [Simulation-based composite likelihood of the site frequency spectrum](../../expected-site-frequency-spectrum/simulation-based-sfs-composite-likelihood.md)

## Expansion

1. Consistency of the ratio estimator of the expected spectrum as the number of simulations grows, as a separate statement.
2. The multi-population forms of the composite likelihood (Equations 5–7): more than two populations, collapsed entries, and the product of pairwise composite likelihoods.
3. Maximization of a simulated objective by conditional maximization, and the effect of Monte Carlo error on the maximizer.

## Sources

- L. Excoffier, I. Dupanloup, E. Huerta-Sánchez, V. C. Sousa and M. Foll, Robust demographic inference from genomic and SNP data, PLoS Genet. 9 (2013), e1003905, Methods (Equations 1–3 for one population, 4 for two populations, 5–7 for more than two populations). <https://doi.org/10.1371/journal.pgen.1003905>
