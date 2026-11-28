# Familial relative risk explained under a log-additive model

Let a disease have overall familial relative risk $\lambda > 1$ for first-degree relatives. Let independent loci $i = 1, \dots, m$ have risk-allele frequency $p_i$ and per-allele log odds ratio $\beta_i$, acting multiplicatively on risk (log-additive model), with estimates $\hat\beta_i$ of standard error $\tau_i$. Each locus contributes a familial relative risk $\lambda_i$ with

$$\ln \lambda_i \approx p_i (1 - p_i)\, \beta_i^2,$$

and the proportion of the familial risk explained by the loci is estimated by

$$\lambda_g = \frac{\sum_{i=1}^{m} p_i (1 - p_i)\bigl(\hat\beta_i^2 - \tau_i^2\bigr)}{\ln \lambda}.$$

## Depends on

- [Multiplicative model: $\lambda_R$ is the product of the locus ratios](recurrence-ratio-pi.md)

## Expansion

Under a multiplicative model the familial relative risk factorizes over independent loci, $\lambda_{\mathrm{loci}} = \prod_i \lambda_i$, so log familial risks add and the explained share is $\sum_i \ln \lambda_i / \ln \lambda$. For one locus with genotype count $G \in \{0, 1, 2\}$ and risk proportional to $e^{\beta G}$, the log-risk score has variance $2p(1-p)\beta^2$ under Hardy–Weinberg equilibrium; first-degree relatives share half of an additive score, so the covariance of their log-risks is $p(1-p)\beta^2$, and for a rare disease with small effects $\ln \lambda_i$ is approximately this covariance. The correction $\hat\beta_i^2 - \tau_i^2$ removes the upward bias of squared estimates, since $E[\hat\beta_i^2] = \beta_i^2 + \tau_i^2$ for an unbiased estimate. With an assumed familial relative risk of $4.93$ for myeloproliferative neoplasms, 17 GWAS loci were estimated to explain 18.4% of the familial relative risk.

## Sources

- E. L. Bao, S. K. Nandakumar, X. Liao, A. G. Bick, J. Karjalainen, M. Tabaka et al., "Inherited myeloproliferative neoplasm risk affects haematopoietic stem cells", Nature (2020), Methods "Contribution of variants to overall familial relative risk", <https://doi.org/10.1038/s41586-020-2786-7>, PMCID PMC7606745.
