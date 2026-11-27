# Chimeric epistasis as a joint cumulant

**Setting.** As for multiplicative epistasis, $f_T$ is the fitness of the genotype mutated exactly at $T \subseteq \{1,\dots,L\}$, normalised so that the wild type has $f_\emptyset = 1$. The *chimeric* epistasis formulae measure deviation from a multiplicative null model as a difference rather than a ratio; for two and three loci

$$\epsilon^{C}_{ij} = f_{ij} - f_i f_j, \qquad \epsilon^{C}_{ijk} = f_{ijk} - f_{ij}f_k - f_{ik}f_j - f_{jk}f_i + 2 f_i f_j f_k .$$

**Moment interpretation.** Suppose $f_T = E\big[\prod_{i \in T} X_i\big]$ are the moments of a multivariate Bernoulli vector $X = (X_1,\dots,X_L)$. Then the $K$-th order chimeric measure is the joint cumulant

$$\epsilon^{C}_{i_1 \cdots i_K} = \kappa(X_{i_1},\dots,X_{i_K}) = \sum_{\pi} (|\pi| - 1)!\,(-1)^{|\pi|-1}\prod_{B \in \pi} E\Big[\prod_{i \in B} X_i\Big],$$

the sum running over set partitions $\pi$ of $\{i_1,\dots,i_K\}$; for $K = 2, 3$ this reproduces the formulae above.

**Consequences.**

- The moment assumption makes the fitness of one genotype a sum of probabilities of several genotypes, e.g. for $L = 4$, $f_{1100} = E[X_1X_2] = p_{1100} + p_{1101} + p_{1110} + p_{1111}$.
- For pairs, $\epsilon^C_{ij} \approx \log \epsilon^M_{ij} = \log f_{ij} - \log f_i - \log f_j$ when all three fitness values are close to $1$, but the two can differ in magnitude otherwise.
- For three or more loci the joint cumulant and the natural parameter $\beta_S$ (the multiplicative measure) measure different kinds of dependence: cumulants detect additive common components, natural parameters multiplicative changes in genotype probabilities. In particular a vanishing higher-order cumulant does not imply the absence of a higher-order log-linear interaction, and vice versa, so chimeric and multiplicative measures can disagree in sign.

## Depends on

- [Multiplicative epistasis equals the natural parameters of a multivariate Bernoulli distribution](multiplicative-epistasis-equals-mvb-natural-parameters.md)
- [Joint-cumulant reparametrization of haplotype frequencies](../../statistical-genetics/association-tests/hierarchical-linkage-disequilibrium/joint-cumulant-reparametrization-of-haplotype-frequencies.md)

## Expansion

For $K = 2$ the partitions of $\{i,j\}$ are $\{\{i,j\}\}$ and $\{\{i\},\{j\}\}$, giving $E[X_iX_j] - E[X_i]E[X_j] = f_{ij} - f_if_j$. For $K = 3$ the single-block partition contributes $f_{ijk}$, the three two-block partitions contribute $-f_{ij}f_k$ and its permutations, and the all-singleton partition contributes $2! f_if_jf_k$. Writing $f = 1 + \delta$ with small $\delta$ shows the pairwise chimeric and log-multiplicative measures agree to first order. In simulations from multiplicative fitness models with noise, and in yeast triple-knockout, E. coli drug-combination and deep mutational scanning data, roughly 10% to 60% of inferred higher-order interactions change sign between the two measures.

## Sources

- U. Chitra, B. Arnold, B. J. Raphael, "Resolving discrepancies between chimeric and multiplicative measures of higher-order epistasis", Nature Communications (2025), Table 1, Eq. (6), Fig. 1 and Methods, <https://doi.org/10.1038/s41467-025-56986-5>, PMCID PMC11833126.
