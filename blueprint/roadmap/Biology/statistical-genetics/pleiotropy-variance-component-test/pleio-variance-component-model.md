# PLEIO variance-component model for multi-trait summary statistics

Fix a SNP $i$ and $T$ studies. Let $\hat\eta_i \in \mathbb R^T$ be its standardized marginal effect estimates (for a quantitative trait, $\hat\eta_{it} = (\hat\beta_{it}/\mathrm{SE}[\hat\beta_{it}])/\sqrt{N_t}$; binary traits are rescaled to the liability scale, Eq. (1) of the source). Let $\Omega$ be the $T \times T$ genetic covariance matrix (diagonal entries the SNP heritabilities, off-diagonal entries built from genetic correlations) and let $C_e$ be the error correlation matrix, both estimated by cross-trait LD-score regression. The model is

$$\hat\eta_i = \gamma_i + \epsilon_i, \qquad \gamma_i \sim \mathrm{MVN}(0, \tau_i^2 \Omega), \qquad \epsilon_i \sim \mathrm{MVN}(0, \Sigma),$$

with $\Sigma = \mathrm{diag}(\mathrm{SE}[\hat\eta_i])\, C_e\, \mathrm{diag}(\mathrm{SE}[\hat\eta_i])$ and $\gamma_i, \epsilon_i$ independent, so $\hat\eta_i \sim \mathrm{MVN}(0, \tau_i^2 \Omega + \Sigma)$. The SNP is pleiotropic-causal when $\tau_i^2 > 0$; PLEIO tests $H_0 : \tau_i^2 = 0$ against $H_1 : \tau_i^2 > 0$.

Taking $\tau_i^2 = 1/K$ for each of $K$ equally contributing causal SNPs and $\tau_i^2 = 0$ otherwise recovers the infinitesimal model $\eta_i \sim \mathrm{MVN}(0, \Omega/K)$.

## Depends on

- [Bivariate LD-score model](../genomic-prediction-from-summary-statistics/cross-trait-model.md)

## Expansion

The genetic part is a random effect whose covariance is proportional to the genome-wide genetic covariance, so traits with larger heritability carry larger effects and effects across traits are correlated as the genetic correlations dictate; only the per-SNP scale $\tau_i^2$ is free. Correlated errors from sample overlap enter through $C_e$, which is why the test controls false positives when studies share individuals (Section "Step 3" of Material and methods).

## Sources

- C. H. Lee, H. Shi, B. Pasaniuc, E. Eskin and B. Han, PLEIO: a method to map and interpret pleiotropic loci with GWAS summary statistics, American Journal of Human Genetics 108 (2021), 36-48. <https://doi.org/10.1016/j.ajhg.2020.11.017> (PMCID PMC7820744)
