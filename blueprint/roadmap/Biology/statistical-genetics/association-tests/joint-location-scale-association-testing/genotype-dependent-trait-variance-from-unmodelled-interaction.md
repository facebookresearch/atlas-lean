# Genotype-dependent trait variance from unmodelled interaction

**Model.** Let $G \in \{0,1,2\}$ be the minor-allele count at a SNP, $E$ an exposure (environmental or genetic background) with $E$ independent of $G$ and $\operatorname{Var}(E) = 1$, and let the quantitative trait follow

$$Y = \beta_0 + \beta_G G + \beta_E E + \beta_{GE}\,GE + \varepsilon, \qquad \varepsilon \sim N(0,1) \text{ independent of } (G,E).$$

**Proposition.** If $E$ is not measured and $Y$ is analysed against $G$ alone, then

$$\sigma_g^2 = \operatorname{Var}(Y \mid G = g) = (\beta_E + \beta_{GE}\,g)^2 + 1, \qquad g = 0,1,2.$$

Hence the genotype-specific variances are unequal whenever $\beta_{GE} \ne 0$, even if $\beta_G = 0$, and the working model $Y = \beta_0 + \beta_G G + \varepsilon_G$ is heteroscedastic.

## Depends on

Its statement uses only the notions recalled above.

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

Conditionally on $G = g$, $Y - \beta_0 - \beta_G g = (\beta_E + \beta_{GE}g)E + \varepsilon$, a sum of independent terms with variances $(\beta_E+\beta_{GE}g)^2\operatorname{Var}(E)$ and $1$. A variance difference across genotypes is therefore a footprint of interaction with an unobserved factor, which motivates scale tests (Levene's test across genotype groups) as a screen for interacting loci, and joint location-scale tests that keep power when the main effect is small.

## Sources

- D. Soave, H. Corvol, N. Panjwani, J. Gong, W. Li, P.-Y. Boëlle, P. R. Durie, A. D. Paterson, J. M. Rommens, L. J. Strug, L. Sun, "A joint location-scale test improves power to detect associated SNPs, gene sets, and pathways", American Journal of Human Genetics 97(1) (2015) 125–138, Material and Methods (genetic model and notation), Equations 1–2, following Paré et al. (2010), <https://doi.org/10.1016/j.ajhg.2015.05.015>, PMCID PMC4572492.
