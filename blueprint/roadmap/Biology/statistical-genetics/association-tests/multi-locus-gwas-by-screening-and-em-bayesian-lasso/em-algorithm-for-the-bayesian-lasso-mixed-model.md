# EM algorithm for the multi-locus Bayesian LASSO mixed model

Consider the multi-locus linear mixed model

$$Y = \sum_{j=1}^{q} X_j \beta_j + \sum_{k=1}^{p} Z_k \gamma_k + \varepsilon, \qquad \varepsilon \sim \mathrm{MVN}_n(0, \sigma^2 I_n),$$

where $\beta_j$ are fixed effects (mean, population structure) with design $X = (X_1, \dots, X_q)$, $\gamma_k \in \mathbb{R}^{m_k}$ is the effect vector of locus $k$ with incidence matrix $Z_k$, and $\gamma_k \sim \mathrm{MVN}_{m_k}(0, \sigma_k^2 I_{m_k})$ independently, with a hierarchical (lasso-inducing) prior on each $\sigma_k^2$. Treating the $\gamma_k$ as missing data, write

$$V = \sum_{k=1}^{p} Z_k Z_k^{\mathsf T} \sigma_k^2 + I \sigma^2 .$$

Given the current variance components, the fixed effects are the generalized least-squares estimate $\hat\beta = (X^{\mathsf T} V^{-1} X)^{-1} X^{\mathsf T} V^{-1} Y$, and the E-step quantities are

$$\mathbb{E}(\gamma_k) = \sigma_k^2 Z_k^{\mathsf T} V^{-1} (Y - X\beta), \qquad \operatorname{var}(\gamma_k) = I \sigma_k^2 - \sigma_k^2 Z_k^{\mathsf T} V^{-1} Z_k \sigma_k^2,$$

$$\mathbb{E}(\gamma_k^{\mathsf T}\gamma_k) = \mathbb{E}(\gamma_k)^{\mathsf T} \mathbb{E}(\gamma_k) + \operatorname{tr}[\operatorname{var}(\gamma_k)],$$

with the residual variance updated as $\hat\sigma^2 = \frac{1}{n} (Y - X\beta)^{\mathsf T}\bigl[(Y - X\beta) - \sum_k Z_k \mathbb{E}(\gamma_k)\bigr]$. The M-step updates each $\sigma_k^2$ from $\mathbb{E}(\gamma_k^{\mathsf T}\gamma_k)$ according to its hyperprior, and loci whose $\hat\gamma_k$ shrink to zero are dropped.

## Proof depends on

- [Gaussian conditioning (Schur complement)](../../../../Probability/distributions/continuous/gaussian-conditioning/cond-distrib-multivariate-gaussian.md)

## Expansion

Conditionally on the variance components, $(\gamma_k, Y)$ is jointly Gaussian with $\operatorname{cov}(\gamma_k, Y) = \sigma_k^2 Z_k^{\mathsf T}$ and $\operatorname{var}(Y) = V$, so the conditional mean and variance above are the standard Gaussian conditioning formulas (best linear unbiased prediction of random effects). The second moment $\mathbb{E}(\gamma_k^{\mathsf T}\gamma_k)$ is what the complete-data log-posterior of $\sigma_k^2$ needs, so the M-step is closed form for conjugate-type hyperpriors. A heavy-tailed marginal prior on $\gamma_k$, obtained by mixing the normal over an exponential or scaled inverse-$\chi^2$ prior on $\sigma_k^2$, shrinks small effects strongly while leaving large ones almost untouched, which is how the method performs selection and estimation jointly on the SNPs that survive screening.

## Sources

- Tamba CL, Ni YL, Zhang YM. Iterative sure independence screening EM-Bayesian LASSO algorithm for multi-locus genome-wide association studies. *PLoS Computational Biology* (2017), Methods, "EM-Bayesian LASSO (EM-BLASSO)", equations (5)–(7). DOI <https://doi.org/10.1371/journal.pcbi.1005357>. PMCID PMC5308866.
- Xu S. An expectation-maximization algorithm for the Lasso estimation of quantitative trait locus effects. *Heredity* 105:483–494 (2010). DOI <https://doi.org/10.1038/hdy.2009.180>.
