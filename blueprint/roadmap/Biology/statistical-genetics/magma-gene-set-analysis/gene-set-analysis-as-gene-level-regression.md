# Gene-set analysis as gene-level regression

Let $Z = (z_g)$ be the vector of gene $z$-values from the [gene test](principal-components-regression-gene-test.md). MAGMA models

$$Z = \beta_0 \mathbf{1} + C_1 \beta_1 + C_2 \beta_2 + \dots + \varepsilon, \qquad \varepsilon \sim \mathrm{MVN}(0, \sigma^2 R),$$

where the $C_k$ are gene properties and $R$ is a gene–gene correlation matrix, and fits it by generalized least squares. Two special cases define the gene-set tests for a set $s$:

- **Self-contained**: $Z_s = \beta_0 \mathbf{1} + \varepsilon_s$ on the genes of $s$, with $R_s$ the corresponding submatrix of $R$ and $\sigma^2 = 1$; test $\beta_0 = 0$ against $\beta_0 > 0$.
- **Competitive**: $Z = \beta_{0s} \mathbf{1} + S_s \beta_s + \varepsilon$ over all genes, with $S_s$ the indicator of membership in $s$; test $\beta_s = 0$ against $\beta_s > 0$.

With $R = I$ these are a one-sided one-sample $t$-test of the mean $z$ in $s$ against $0$ and a one-sided two-sample $t$-test of genes in $s$ against genes outside $s$. $R$ is approximated by the correlations, under the joint null of no association, between the model sums of squares of the gene regressions, which depend on the linkage disequilibrium between the genes' SNPs. By default the competitive test also includes gene size, gene density and their logarithms as covariates.

## Depends on

- [Principal-components regression gene test](principal-components-regression-gene-test.md)

## Expansion

Under the self-contained null every $z_g$ is standard normal, which fixes $\sigma^2 = 1$; neighbouring genes in linkage disequilibrium have correlated $z$-values, which the GLS error covariance $R$ accounts for. Any gene-level covariate, transformation or interaction can be added to the same regression, which gives conditional and joint gene-set tests.

## Sources

- C. A. de Leeuw et al., *MAGMA: generalized gene-set analysis of GWAS data*, PLoS Comput. Biol. 11 (2015), e1004219. <https://doi.org/10.1371/journal.pcbi.1004219> (PMCID: PMC4401657) Methods, "Gene-set analysis".
