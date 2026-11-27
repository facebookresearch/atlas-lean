# Burden TWAS Z-score from GWAS summary statistics

Let a gene $g$ have expression weights $\hat w_{lg}$ on SNPs $l$ in its prediction model $\mathrm{Model}_g$ (for BGW-TWAS, $\hat w_{lg} = \widehat{\mathrm{PP}}_l\, \hat w_l$; see [Bayesian GReX](bayesian-genetically-regulated-expression.md)). From a GWAS based on single-variant tests take, for each SNP, the marginal effect $\hat\beta_l$, its standard error $\mathrm{SE}(\hat\beta_l)$ and $Z_l = \hat\beta_l / \mathrm{SE}(\hat\beta_l)$. From a reference panel of matching ancestry let $V = \operatorname{Cov}(X)$ be the genotype covariance matrix of the model SNPs, $\hat\sigma_l^2 = V_{ll}$ the genotype variance of SNP $l$, and

$$\hat\sigma_g^2 = \hat w^{\top} V \hat w$$

the variance of the imputed expression.

**Definition (S-PrediXcan burden statistic, used by BGW-TWAS).**

$$Z_g = \sum_{l \in \mathrm{Model}_g} \hat w_{lg}\, \frac{\hat\sigma_l}{\hat\sigma_g}\, Z_l = \frac{\sum_{l \in \mathrm{Model}_g} \hat w_{lg}\, \hat\sigma_l\, Z_l}{\sqrt{\hat w^{\top} V \hat w}}.$$

**Proposition.** Suppose that under the null hypothesis of no association the vector $(Z_l)_{l \in \mathrm{Model}_g}$ is multivariate normal with mean zero and covariance equal to the SNP correlation matrix $R$, $R_{lm} = V_{lm} / (\hat\sigma_l \hat\sigma_m)$, and the weights are fixed (estimated from an independent reference sample). Then $Z_g \sim \mathcal{N}(0, 1)$ under the null.

## Depends on

- [Bayesian genetically regulated expression with cis- and trans-eQTL spike-and-slab priors](bayesian-genetically-regulated-expression.md)

## Expansion

Put $a_l = \hat w_{lg} \hat\sigma_l$. Then $\sum_l a_l Z_l$ is normal with mean zero and variance $\sum_{l,m} a_l a_m R_{lm} = \sum_{l,m} \hat w_{lg} \hat w_{mg} V_{lm} = \hat w^{\top} V \hat w$, so dividing by $\hat\sigma_g$ standardizes it. The statistic is the summary-data analogue of regressing the phenotype on imputed expression: the covariance of the phenotype with $\sum_l \hat w_{lg} X_l$ is $\sum_l \hat w_{lg} \operatorname{Cov}(X_l, Y)$, and each marginal covariance is proportional to $\hat\sigma_l Z_l$ when per-SNP sample sizes and phenotype variance are constant. Including trans-eQTL simply enlarges $\mathrm{Model}_g$; $V$ is block-diagonal across approximately independent genome blocks.

## Sources

- J. M. Luningham, J. Chen, S. Tang, et al., "Bayesian Genome-wide TWAS Method to Leverage both cis- and trans-eQTL Information through Summary Statistics", American Journal of Human Genetics 107 (2020), 714–726, section "BGW-TWAS with Summary-Level GWAS Data", <https://doi.org/10.1016/j.ajhg.2020.08.022> (PMC7536614).
