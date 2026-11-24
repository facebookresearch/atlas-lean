# Simulation-based fitting of site-frequency spectra (fastsimcoal2)

Excoffier, Dupanloup, Huerta-Sánchez, Sousa and Foll (2013, Materials and Methods) estimate the expected site-frequency spectrum by coalescent simulation. For one genealogy, the probability that a mutation has derived frequency $i$ is the ratio of the total length of the branches subtending exactly $i$ sampled leaves to the total tree length (their Equation 1); over $Z$ simulated genealogies they estimate it by the ratio of the summed lengths of the qualifying branches to the summed total lengths (Equation 2), which weights each genealogy by the probability that it carries a mutation. These probabilities enter a composite multinomial likelihood that also uses the numbers of monomorphic and polymorphic sites through the probability of no mutation on the tree under Poisson mutation (Equation 3), with versions for the joint spectrum of two or more populations, collapsing of rarely observed entries, and a product of pairwise composite likelihoods for many populations (Equations 4–7). Because the likelihood is estimated by simulation, it is maximized by a conditional maximization (ECM) algorithm, one parameter at a time with Brent's method. For a bottleneck and a split without migration, where the expected spectrum can be computed exactly, the estimated entries scatter symmetrically around the exact values as the number of simulations grows (Figures S14 and S15).

## Expansion

1. The derived-frequency probability of a mutation on a fixed genealogy as a branch-length ratio (Equation 1).
2. The ratio estimator over simulated genealogies (Equation 2), its length weighting, and its consistency as the number of simulations grows, as a separate statement.
3. The composite multinomial likelihood with monomorphic sites (Equation 3) and its multi-population forms (Equations 4–7).
4. Maximization of a simulated objective by conditional maximization, and the effect of Monte Carlo error on the maximizer.

## Sources

- L. Excoffier, I. Dupanloup, E. Huerta-Sánchez, V. C. Sousa and M. Foll, Robust demographic inference from genomic and SNP data, PLoS Genet. 9 (2013), e1003905, Materials and Methods (Equations 1–7). <https://doi.org/10.1371/journal.pgen.1003905>
