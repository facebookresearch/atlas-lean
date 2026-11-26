# LD-residual genetic relationship matrix

Let $X$ be the $N \times M$ matrix of standardized genotypes (columns $x_1, \dots, x_M$ with mean $0$ and variance $1$) of $N$ individuals at $M$ ordered SNPs. For each SNP $j$ let $P(j)$ be the set of preceding SNPs within a fixed physical window (100 kb for genotyped, 500 kb for imputed data), after removing one SNP of each near-perfectly correlated pair so that $X_{P(j)}^\top X_{P(j)}$ is invertible. The LD residual of SNP $j$ is the least-squares residual

$$\tilde x_j = x_j - X_{P(j)}\bigl(X_{P(j)}^\top X_{P(j)}\bigr)^{-1} X_{P(j)}^\top x_j,$$

and the LD-residual genetic relationship matrix is

$$\tilde A = \frac{\tilde X \tilde X^\top}{\sum_{j=1}^{M} \widehat{\operatorname{var}}(\tilde x_j)}, \qquad \tilde X = (\tilde x_1, \dots, \tilde x_M).$$

Each $\tilde x_j$ is orthogonal to the span of its preceding markers. Heritability is then estimated by REML in the variance-component model $y = Z\gamma + g + e$ with $\operatorname{Cov}(g) = \sigma_g^2 \tilde A$, $\operatorname{Cov}(e) = \sigma_e^2 I$ and $h^2 = \sigma_g^2/(\sigma_g^2 + \sigma_e^2)$, applied either genome-wide or to the SNPs of one locus.

## Depends on

- [Genetic relationship matrix entry](grm.md)

## Expansion

For two markers with correlation $r$, the residual of the second has variance $1 - r^2$, so a marker in perfect linkage disequilibrium with its predecessor contributes nothing and a nearly independent one contributes fully; this equalizes the representation of each independent signal in the relationship matrix. Because residuals no longer have unit variance, the normalization uses the sum of their empirical variances instead of $M$. The adjustment addresses the bias of the standard GRM when causal variants are not a random subset of the typed SNPs (for example when they are of low frequency and tagged by few markers): in simulations the standard estimate fell to about 0.50 to 0.55 of a true value of 0.80 when causal variants were uncommon, while the LD-residual estimate removed most of the bias without significant upward inflation. Applied at known GWAS loci for nine traits, it showed that local SNP-heritability exceeds what the reported lead SNPs explain.

## Sources

- A. Gusev, G. Bhatia, N. Zaitlen, B. J. Vilhjalmsson, D. Diogo, E. A. Stahl, et al., "Quantifying missing heritability at known GWAS loci", *PLoS Genetics* 9 (2013), e1003993, Methods sections "Variance-components model" and "Transformation by linear regression (LD-residual)", <https://doi.org/10.1371/journal.pgen.1003993> (PMC3873246).
