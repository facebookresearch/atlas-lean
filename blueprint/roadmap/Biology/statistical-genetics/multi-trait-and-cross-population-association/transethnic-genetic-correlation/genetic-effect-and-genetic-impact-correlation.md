# Genetic-effect and genetic-impact correlation

Let $M$ SNPs be shared by two populations with allele-frequency vectors $f_1,f_2$. Under Hardy–Weinberg equilibrium within each population the per-SNP genotype variances are $\sigma_p^2=2f_p(1-f_p)$, $p=1,2$. Let $\beta_1,\beta_2\in\mathbb R^M$ be the per-allele effect sizes of the SNPs on the same trait in the two populations, so the heritability in population $p$ is $h_p^2=\sum_i\sigma_{pi}^2\beta_{pi}^2$. Treating the effects as random across SNPs, define

$$\rho_{ge}=\operatorname{Cor}(\beta_1,\beta_2),\qquad \rho_{gi}=\operatorname{Cor}(\sigma_1\beta_1,\ \sigma_2\beta_2).$$

The genetic-effect correlation $\rho_{ge}$ compares per-allele effects; the genetic-impact correlation $\rho_{gi}$ compares effects on standardised genotypes, which weight each SNP by its contribution to phenotypic variance in each population.

## Expansion

The two notions differ whenever allele frequencies differ. A SNP with identical per-allele effect that is rare in one population and common in the other contributes perfect agreement to $\rho_{ge}$ but very different variance contributions, lowering $\rho_{gi}$. Conversely, effects that are large where the allele is rare and small where it is common can give low $\rho_{ge}$ but similar impact, raising $\rho_{gi}$. If effects scale as $1/\sigma$, then $\rho_{gi}$ is the natural parameter; if effects are independent of allele frequency, $\rho_{ge}$ is.

## Sources

- B. C. Brown et al., "Transethnic Genetic-Correlation Estimates from Summary Statistics", Am. J. Hum. Genet. 99 (2016), 76–88, Introduction and Material and Methods, <https://doi.org/10.1016/j.ajhg.2016.05.001>, PMCID PMC5005434.
