# Saddlepoint approximation of the logistic mixed-model score test

In the setting of the [variance-ratio adjusted score test](variance-ratio-adjusted-score-test.md), condition on the null fit $\hat b$, so that $\tilde G^\top Y$ is a weighted sum of independent Bernoulli$(\hat\mu_i)$ variables. With $c = \operatorname{Var}^*(T)^{-1/2}$, the cumulant generating function used for the standardized score is

$$K(t) = \sum_{i=1}^{N} \log\bigl(1 - \hat\mu_i + \hat\mu_i e^{c t \tilde G_i}\bigr) - c t \sum_{i=1}^{N} \tilde G_i \hat\mu_i.$$

For an observed value $q$, let $\hat\zeta$ solve $K'(\hat\zeta) = q$, and set

$$w = \operatorname{sign}(\hat\zeta)\bigl[2\{\hat\zeta q - K(\hat\zeta)\}\bigr]^{1/2}, \qquad v = \hat\zeta \{K''(\hat\zeta)\}^{1/2}.$$

Then the null tail probability is approximated by the Barndorff-Nielsen formula

$$\Pr(T_{\mathrm{adj}} < q) \approx \Phi\Bigl\{w + \frac{1}{w} \log\frac{v}{w}\Bigr\},$$

where $\Phi$ is the standard normal distribution function. SAIGE uses the normal approximation when $|q|$ is within two standard deviations of the mean and exploits the sparsity of $\tilde G$ for rare variants.

## Depends on

- [Variance-ratio adjusted score test in a logistic mixed model](variance-ratio-adjusted-score-test.md)

## Expansion

The normal approximation uses only the first two cumulants, which fails in the tails when the case–control ratio is unbalanced and the minor allele count is low, because the score is then strongly skewed. The saddlepoint approximation uses the whole cumulant generating function of the Bernoulli sum; $w$ is the signed root of the Legendre transform of $K$ at $q$ and $v$ is the standardized saddlepoint.

## Sources

- W. Zhou et al., *Efficiently controlling for case-control imbalance and sample relatedness in large-scale genetic association studies*, Nat. Genet. 50 (2018), 1335–1341. <https://doi.org/10.1038/s41588-018-0184-y> (PMCID: PMC6119127) Online Methods, "Score test with SPA (Step 2)".
