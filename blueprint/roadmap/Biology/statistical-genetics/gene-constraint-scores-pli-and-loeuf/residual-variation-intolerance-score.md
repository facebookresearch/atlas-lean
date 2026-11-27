# Residual variation intolerance score

Fix a minor-allele-frequency threshold $\rho$ (the paper uses $0.1\%$). For each gene $g = 1, \dots, G$ observed in a population sequencing sample, let

- $Y_g$ be the number of common (MAF $> \rho$) missense and truncating (nonsense and splice) single-nucleotide variants in $g$, and
- $X_g$ be the total number of protein-coding variants in $g$, synonymous included, regardless of frequency.

Fit the ordinary least-squares regression $Y_g = a + bX_g + e_g$ across genes, with fitted coefficients $\hat a, \hat b$ and raw residuals $r_g = Y_g - \hat a - \hat b X_g$. The **residual variation intolerance score** of gene $g$ is the studentized residual

$$S_g = \frac{r_g}{\hat\sigma\sqrt{1 - h_{gg}}},$$

where $\hat\sigma$ is the residual standard deviation and $h_{gg}$ the leverage of gene $g$, i.e. the raw residual divided by an estimate of its standard deviation. $S_g = 0$ means the gene carries the genome-wide average amount of common functional variation given its total mutational burden; $S_g < 0$ (intolerant) means less, typically reflecting purifying selection; $S_g > 0$ means more. By construction

$$\sum_g r_g = 0, \qquad \sum_g X_g r_g = 0,$$

so the raw residuals have zero sample correlation with $X_g$.

## Expansion

The two identities are the least-squares normal equations for the intercept and slope. Studentizing accounts for the larger variability of residuals at larger mutational burdens. Empirically the score showed correlation $0.005$ with $X_g$, consistent with the construction, and genes causing haploinsufficient and de novo Mendelian disease had significantly lower scores. A variant-level refinement (RVIS-PP2) counts as functional only missense variants not predicted benign. Results, "Deriving the Residual Variation Intolerance Score".

## Sources

- S. Petrovski, Q. Wang, E. L. Heinzen, A. S. Allen, D. B. Goldstein, "Genic Intolerance to Functional Variation and the Interpretation of Personal Genomes", PLoS Genetics 9 (2013), e1003709, <https://doi.org/10.1371/journal.pgen.1003709> (PMC3749936).
