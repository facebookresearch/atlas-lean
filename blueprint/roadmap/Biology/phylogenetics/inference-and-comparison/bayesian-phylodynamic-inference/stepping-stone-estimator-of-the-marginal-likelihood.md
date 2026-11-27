# Stepping-stone estimator of the marginal likelihood

Let $L(\theta) = p(D \mid \theta) \ge 0$ be a likelihood and $\pi$ a **proper** prior density on the parameter space (for a phylogenetic model, $\theta$ includes the tree). For $\beta \in [0,1]$ define the **power posterior** and its normalizing constant

$$p_\beta(\theta) = \frac{L(\theta)^\beta\, \pi(\theta)}{Z_\beta}, \qquad Z_\beta = \int L(\theta)^\beta\, \pi(\theta)\, d\theta,$$

so that $Z_0 = 1$ and $Z_1 = p(D)$ is the marginal likelihood. Fix a schedule $0 = \beta_0 < \beta_1 < \dots < \beta_K = 1$, and for each $k = 1,\dots,K$ let $\theta_{k-1,1},\dots,\theta_{k-1,n}$ be draws from $p_{\beta_{k-1}}$. The **stepping-stone estimator** is

$$\widehat{Z}_1 = \prod_{k=1}^{K} \frac{1}{n}\sum_{m=1}^{n} L(\theta_{k-1,m})^{\beta_k - \beta_{k-1}} .$$

**Proposition.**

1. For each $k$, $\displaystyle \frac{Z_{\beta_k}}{Z_{\beta_{k-1}}} = \mathbb{E}_{p_{\beta_{k-1}}}\big[L(\theta)^{\beta_k - \beta_{k-1}}\big]$, and $Z_1 = \prod_{k=1}^K Z_{\beta_k}/Z_{\beta_{k-1}}$.
2. If the draws are exact, with draws for different $k$ independent, then $\widehat Z_1$ is unbiased for $Z_1$.
3. (Path sampling.) If $\mathbb{E}_{p_\beta}|\ln L|$ is finite and integrable in $\beta$, then $\ln Z_1 = \int_0^1 \mathbb{E}_{p_\beta}[\ln L(\theta)]\, d\beta$.

## Remarks

Part 1: $\int L^{\beta_k - \beta_{k-1}}\, L^{\beta_{k-1}}\pi/Z_{\beta_{k-1}} = Z_{\beta_k}/Z_{\beta_{k-1}}$, and the product telescopes with $Z_0 = 1$, which is where properness of the prior is needed. Part 2: each factor is an unbiased sample mean, and the expectation of a product of independent factors is the product of expectations. Part 3: $\frac{d}{d\beta}\ln Z_\beta = \mathbb{E}_{p_\beta}[\ln L]$, integrated from $0$ to $1$. Each stepping-stone ratio is an importance-sampling estimate between neighbouring power posteriors, so it stays accurate when the steps are small, unlike the harmonic-mean estimator. Ratios of marginal likelihoods give Bayes factors for comparing clock, demographic and substitution models; generalized stepping-stone sampling replaces the prior by a working distribution fitted to the posterior to improve accuracy and numerical stability.

## Sources

- M. A. Suchard, P. Lemey, G. Baele, D. L. Ayres, A. J. Drummond and A. Rambaut, "Bayesian phylogenetic and phylodynamic data integration using BEAST 1.10", Virus Evolution 4 (2018) vey016, Section 3 ("Flexible model design", marginal likelihood estimation by path sampling, stepping-stone and generalized stepping-stone sampling), <https://doi.org/10.1093/ve/vey016>, PMCID PMC6007674.
- W. Xie, P. O. Lewis, Y. Fan, L. Kuo and M.-H. Chen, "Improving marginal likelihood estimation for Bayesian phylogenetic model selection", Systematic Biology 60 (2011) 150–160, <https://doi.org/10.1093/sysbio/syq085>.
