# Ratio-of-correlated-gammas regression and its Wald test

Let $(b_i, X_i)$, $i = 1,\dots,n$, be independent observations at one CpG site, with beta value $b_i \in (0,1)$ and covariate vector $X_i = (1, X_{i1},\dots,X_{ip})^{\top}$. The ratio-of-correlated-gammas (RCG) model assumes that, given $X_i$, $b_i$ has the [beta-value density under the Wicksell–Kibble bivariate gamma](beta-value-density-under-the-wicksell-kibble-bivariate-gamma.md) with common shape $\alpha$ and correlation $\rho$, and log-linear rates

$$\log \lambda_m = X^{\top}\zeta_m, \qquad \log \lambda_u = X^{\top}\zeta_u, \qquad \text{so} \quad \log \mathrm{E}(M\mid X) = \log\alpha - X^{\top}\zeta_m,\quad \log \mathrm{E}(U\mid X) = \log\alpha - X^{\top}\zeta_u .$$

With $\gamma = \zeta_m - \zeta_u \in \mathbb{R}^{p+1}$ the mean ratio is $\theta \mid X = \mathrm{E}(U\mid X)/\mathrm{E}(M\mid X) = \exp(X^{\top}\gamma)$, and the log-likelihood is

$$\ell(\alpha,\rho,\gamma) = \sum_{i=1}^n \Bigl[\log\Gamma(2\alpha) - 2\log\Gamma(\alpha) + \alpha X_i^{\top}\gamma + \alpha\log(1-\rho) + \log\bigl((e^{X_i^{\top}\gamma}-1)b_i + 1\bigr) + (\alpha-1)\log\bigl(b_i(1-b_i)\bigr) - \bigl(\alpha+\tfrac12\bigr)\log\Bigl(\bigl((e^{X_i^{\top}\gamma}-1)b_i+1\bigr)^2 - 4\rho\, e^{X_i^{\top}\gamma} b_i(1-b_i)\Bigr)\Bigr].$$

So the likelihood identifies only the contrast $\gamma$, not $\zeta_m$ and $\zeta_u$ separately. A covariate $X_k$ is unassociated with methylation exactly when it multiplies $\mathrm{E}(M\mid X)$ and $\mathrm{E}(U\mid X)$ by the same factor, that is when $\gamma_k = 0$. For maximum-likelihood estimates $(\hat\alpha,\hat\rho,\hat\gamma)$ and observed information $J = -\partial^2\ell/\partial\gamma\,\partial\gamma^{\top}$ evaluated there, the Wald statistic

$$Z_k = \frac{\hat\gamma_k}{\sqrt{(J^{-1})_{kk}}}$$

is asymptotically standard normal under $H_0: \gamma_k = 0$ as $n \to \infty$, under the usual regularity conditions for maximum likelihood.

## Depends on

- [Beta-value density under the Wicksell–Kibble bivariate gamma](beta-value-density-under-the-wicksell-kibble-bivariate-gamma.md)

## Expansion

Substituting $\theta_i = \exp(X_i^{\top}\gamma)$ into the $\theta$-form of the beta-value density and summing logarithms gives $\ell$. Since $\theta$ is a ratio of the two means, any common shift of $\zeta_m$ and $\zeta_u$ cancels, which is why only $\gamma$ enters. Unlike beta regression, where $M$ and $U$ are independent with a common rate, the parameter $\rho$ absorbs the positive correlation between the two channels that arrays show at most sites. The authors maximize $\ell$ jointly over $\gamma$, $\alpha$ and $\rho$ by gradient boosting with linear base learners; the Wald test is then the standard asymptotic one.

## Sources

- L. Weinhold, S. Wahl, S. Pechlivanis, P. Hoffmann and M. Schmid, "A statistical model for the analysis of beta values in DNA methylation studies", BMC Bioinformatics 17 (2016), 480, <https://doi.org/10.1186/s12859-016-1347-4>, PMCID PMC5120494. Eqs. (11)–(14).
