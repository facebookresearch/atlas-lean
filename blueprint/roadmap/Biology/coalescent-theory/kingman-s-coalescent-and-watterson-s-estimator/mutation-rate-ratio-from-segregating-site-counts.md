# Mutation-rate ratio from segregating-site counts

Let a sample of $n$ genomes share one genealogy at each position, and consider two classes of mutational events acting independently on the same genealogies under the infinite-sites model: class 1 with rate $\mu_1$ per target unit over $L_1$ target units, class 2 with rate $\mu_2$ per unit over $L_2$ units (for example single-nucleotide substitutions, with targets single sites, and adjacent multi-nucleotide substitutions, with targets dinucleotides). Let $S_1, S_2$ be the numbers of segregating sites of each class. If the expected total branch length $E[L_{\mathrm{tree}}]$ is the same for both classes, then

$$E[S_c] = \mu_c L_c\, E[L_{\mathrm{tree}}] \quad (c = 1, 2), \qquad \text{hence} \qquad \frac{E[S_2]}{E[S_1]} = \frac{\mu_2 L_2}{\mu_1 L_1},$$

and, when $S_1 > 0$, the moment estimator

$$\hat\mu_2 = \mu_1 \cdot \frac{S_2 / L_2}{S_1 / L_1}$$

converts a known per-site rate of one class into the rate of the other by equating the observed ratio of counts to the ratio of their expectations. The genealogy, effective population size and sample size cancel from the ratio of expectations; only the class-specific target sizes and the counts are needed. The cancellation concerns the population means, not $\hat\mu_2$ itself: $E[S_2/S_1]$ is in general not $E[S_2]/E[S_1]$, and under the Poisson model $S_1 = 0$ has positive probability, where the estimator is undefined.

## Depends on

- [Expected number of segregating sites](integral-seg-sites.md)
- [Watterson's estimator is unbiased](watterson-unbiased.md)

## Expansion

Conditionally on the genealogy, each class places mutations as a Poisson process on the branches with intensity $\mu_c L_c$ per unit branch length, so $E[S_c \mid \text{tree}] = \mu_c L_c L_{\mathrm{tree}}$, and taking expectations gives the identity; equivalently, the expectations of Watterson's estimates $\hat\theta_c = S_c / H_{n-1}$ stand in the ratio $\mu_2 L_2 / (\mu_1 L_1)$. The key assumptions are neutrality of both classes (or equal selection), no recurrent mutation, and that a multi-nucleotide event is counted only when it arose in one generation, which in population data is enforced by keeping adjacent variant pairs whose constituent alleles have identical frequencies. Since a genome has about as many dinucleotide positions as sites ($L_2 \approx L_1$), the estimator reduces to $\hat\mu_2 = \mu_1 S_2 / S_1$. With about $1.2 \times 10^{-8}$ per base per generation for single-nucleotide substitutions, the ratio of adjacent multi-nucleotide variant sites to single-nucleotide variant sites in 125,748 exomes and 15,708 genomes gave about $2.94 \times 10^{-11}$ adjacent multi-nucleotide events per dinucleotide per generation, roughly two thirds of a trio-based estimate; per-pattern rates follow by rescaling with the number of reference dinucleotides of each type and coverage.

## Sources

- Q. Wang, E. Pierce-Hoffman, B. B. Cummings, J. Alföldi, L. C. Francioli, L. D. Gauthier et al., "Landscape of multi-nucleotide variants in 125,748 human exomes and 15,708 genomes", Nature Communications (2020), Methods "Defining one-step MNVs and MNVs in repetitive context" and "Estimation of the global MNV rate per substitution pattern", <https://doi.org/10.1038/s41467-019-12438-5>, PMCID PMC7253413.
