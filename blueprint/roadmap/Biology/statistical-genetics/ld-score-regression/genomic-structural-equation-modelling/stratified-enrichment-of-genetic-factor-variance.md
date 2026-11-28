# Stratified enrichment of genetic factor variance

Let a genomic SEM factor model with loadings $\Lambda$ be fitted to the genome-wide genetic covariance matrix of $k$ traits over $M$ SNPs. For a functional annotation $A$ containing $M_A$ of the SNPs, stratified multivariable LD-score regression gives an annotation-specific genetic covariance matrix $S_A$ and its sampling covariance.

**Procedure.** Fix $\Lambda$ at its genome-wide estimate and re-estimate, within annotation $A$, only the factor variances $\phi_{f,A}$ and the residual genetic variances $\theta_{t,A}$, scaled to be comparable to the genome-wide estimates $\phi_f$ and $\theta_t$.

**Enrichment.** The enrichment of factor $f$ in $A$ is the ratio of ratios

$$E_{f,A} = \frac{\phi_{f,A}/\phi_f}{M_A/M},$$

and the residual enrichment of trait $t$ is defined in the same way from $\theta_{t,A}$. The null value is $1$; $E_{f,A} > 1$ means the annotation carries a share of the factor's genetic variance larger than its share of SNPs.

## Depends on

- [Genomic SEM factor model and SNP heterogeneity test](genomic-sem-factor-model-and-snp-heterogeneity-test.md)
- [Heritability enrichment of a category](../../stratified-ld-score-regression/enrichment.md)

## Expansion

Holding the loadings fixed makes the factor mean the same thing in every annotation, so a change in its variance is attributable to the annotation rather than to a re-definition of the factor. For a single trait with $\Lambda$ the identity and $\Theta = 0$, $E_{f,A}$ reduces to the usual stratified LD-score heritability enrichment. Applied to 162 annotations and 11 factor or residual variance components in psychiatric disorders, with a Bonferroni threshold of $2.81\times10^{-5}$, the method localizes shared genetic variance to annotations such as the intersection of genes intolerant to protein-truncating variants with neuronal cell types.

## Sources

- A. D. Grotzinger, J. Werme, W. J. Peyrot et al., "Mapping the genetic landscape across 14 psychiatric disorders", Nature (2025), Methods ("Stratified genomic SEM"), <https://doi.org/10.1038/s41586-025-09820-3>.
