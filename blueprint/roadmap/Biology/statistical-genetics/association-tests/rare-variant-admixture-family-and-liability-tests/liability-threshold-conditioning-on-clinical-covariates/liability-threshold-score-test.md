# Liability threshold score test

Extend the [liability threshold model](posterior-mean-residual-liability.md) by a genotype effect, $\varepsilon = \gamma g + e$ with $e \sim N(0,1)$, so that individual $i$ with mean-centered genotype $g_i$ and covariates $t_i$ is a case with probability $\Phi(\mu(t_i) + \gamma g_i)$. For independent individuals the prospective log-likelihood is

$$\ell(\gamma) = \sum_{i:\, z_i = 1} \log \Phi(\mu_i + \gamma g_i) + \sum_{i:\, z_i = 0} \log\big(1 - \Phi(\mu_i + \gamma g_i)\big), \qquad \mu_i = \mu(t_i),$$

with the covariate parameters $(c, m)$ fixed at values estimated from external prevalence data.

**Proposition.** The score at $\gamma = 0$ is

$$U = \ell'(0) = \sum_i g_i\, \hat\varepsilon_i, \qquad \hat\varepsilon_i = \mathbb{E}[\varepsilon_i \mid z_i, t_i]\big|_{\gamma = 0},$$

the genotype-weighted sum of posterior mean residual liabilities. Under $H_0: \gamma = 0$, $\mathbb{E}[\hat\varepsilon_i \mid t_i] = 0$, so $U$ has mean zero conditionally on the genotypes and covariates; the statistic $U^2 / \widehat{\operatorname{Var}}(U)$, equivalently $n$ times the squared sample correlation between $g$ and $\hat\varepsilon$ (the LT statistic), is asymptotically $\chi^2_1$.

## Depends on

- [Posterior mean residual liability](posterior-mean-residual-liability.md)

## Expansion

Differentiating, $\partial_\gamma \log \Phi(\mu_i + \gamma g_i)|_{0} = g_i \varphi(\mu_i)/\Phi(\mu_i)$ for a case and $\partial_\gamma \log(1 - \Phi(\mu_i + \gamma g_i))|_0 = -g_i \varphi(\mu_i)/(1 - \Phi(\mu_i))$ for a control; these are $g_i$ times the posterior means of the [previous proposition](posterior-mean-residual-liability.md). Under the null, $\mathbb{E}[\hat\varepsilon_i \mid t_i] = \Phi(\mu_i) \cdot \varphi(\mu_i)/\Phi(\mu_i) - (1 - \Phi(\mu_i)) \cdot \varphi(\mu_i)/(1-\Phi(\mu_i)) = 0$. The power gain over logistic regression comes from using externally estimated covariate effects: in covariate-matched designs, logistic regression estimates a covariate effect near zero, while the LT residuals still weight low-risk cases more heavily. Zaitlen et al. report the retrospective likelihood equals this prospective one and that the test keeps its null distribution under mis-specified covariate parameters.

## Sources

- N. Zaitlen, S. Lindström, B. Pasaniuc et al., "Informed conditioning on clinical covariates increases power in case-control association studies", PLoS Genetics 8 (2012), e1003032, Methods "Association test using posterior mean value of underlying quantitative trait" (score-test equivalence) and Results "False-positive rate and correct null distribution", <https://doi.org/10.1371/journal.pgen.1003032>, PMCID PMC3493452.
