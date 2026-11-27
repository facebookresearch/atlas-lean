# Principal-components regression gene test

For a gene $g$, let the SNP genotype matrix of the gene be projected onto its principal components, discard the components with the smallest eigenvalues (by default those carrying the last $0.1\%$ of the variance), and let $X_g$ be the matrix of retained components. With phenotype vector $Y$ and an optional covariate matrix $W$, fit

$$Y = \alpha_{0g} \mathbf{1} + X_g \alpha_g + W \beta_g + \varepsilon_g$$

and test $H_0 : \alpha_g = 0$, conditional on the covariates, with the $F$-test. The gene $p$-value $p_g$ is converted to

$$z_g = \Phi^{-1}(1 - p_g),$$

where $\Phi^{-1}$ is the probit function; $z_g$ is standard normal under the gene's null hypothesis and larger for stronger association.

## Expansion

Using all SNPs jointly accounts for linkage disequilibrium inside the gene; pruning near-zero principal components keeps the model identifiable under collinearity and removes redundant degrees of freedom. The number of retained components is the gene's effective size. The paper reports that the linear $F$-test stays accurate for binary phenotypes when checked against permutation $p$-values.

## Sources

- C. A. de Leeuw et al., *MAGMA: generalized gene-set analysis of GWAS data*, PLoS Comput. Biol. 11 (2015), e1004219. <https://doi.org/10.1371/journal.pcbi.1004219> (PMCID: PMC4401657) Methods, "Gene analysis" and "Gene-set analysis".
