# cML-MR: coordinate descent and BIC model averaging

In the setting of [constrained maximum-likelihood MR](constrained-maximum-likelihood-mr-estimator.md), fix $K$. Starting from $\theta^{(0)}$ and $b_{Xi}^{(0)}$, iteration $k$ performs:

1. **Pleiotropy step.** Order the standardized residuals $(\hat\beta_{Yi} - \theta^{(k)} b_{Xi}^{(k)})^2 / \hat\sigma_{Yi}^2$ decreasingly; for the $K$ largest set $r_i^{(k+1)} = \hat\beta_{Yi} - \theta^{(k)} b_{Xi}^{(k)}$, and set $r_i^{(k+1)} = 0$ for the rest.
2. **Exposure-effect step.**

$$b_{Xi}^{(k+1)} = \frac{\hat\beta_{Xi}/\hat\sigma_{Xi}^2 + \theta^{(k)} (\hat\beta_{Yi} - r_i^{(k+1)})/\hat\sigma_{Yi}^2}{1/\hat\sigma_{Xi}^2 + (\theta^{(k)})^2/\hat\sigma_{Yi}^2}.$$

3. **Causal-effect step.**

$$\theta^{(k+1)} = \frac{\sum_{i=1}^m (\hat\beta_{Yi} - r_i^{(k+1)})\, b_{Xi}^{(k+1)} / \hat\sigma_{Yi}^2}{\sum_{i=1}^m (b_{Xi}^{(k+1)})^2 / \hat\sigma_{Yi}^2}.$$

Each step exactly maximizes the log-likelihood $L$ over its block with the others fixed (step 1 over $\{r_i\}$ under the $\ell_0$ constraint), so $L$ is nondecreasing along the iterates. At a fixed point an instrument with $r_i \ne 0$ has $\hat\beta_{Yi} - r_i = \theta b_{Xi}$, so its terms in step 3 are satisfied by any $\theta$ and it does not inform the estimate of $\theta$.

**Model averaging (cML-MA-BIC).** For $K \in \mathcal K = \{0, 1, \dots, m-2\}$ set $w_K \propto \exp(-\mathrm{BIC}(K)/2)$, normalized to sum to $1$, and

$$\hat\theta_w = \sum_{K \in \mathcal K} w_K\, \hat\theta(K), \qquad \mathrm{SE}(\hat\theta_w) = \sum_{K \in \mathcal K} w_K \sqrt{\mathrm{SE}(\hat\theta(K))^2 + (\hat\theta(K) - \hat\theta_w)^2},$$

where $\mathrm{SE}(\hat\theta(K))^2$ is the $(1,1)$ entry of the inverse Fisher information in $(\theta, \{\beta_{Xi}\}_{i \notin \hat B_K})$.

## Depends on

- [Constrained maximum-likelihood Mendelian randomization (cML-MR)](constrained-maximum-likelihood-mr-estimator.md)

## Expansion

With $\theta$ and $b_X$ fixed, $L$ separates over $i$; freeing $r_i$ removes the $i$-th outcome residual entirely, so the best $K$ to free are those with the largest residuals. With $\theta$ and $r$ fixed, $L$ is a sum of univariate quadratics in $b_{Xi}$, whose minimizers are the precision-weighted means in step 2. With $b_X$ and $r$ fixed, $L$ is a weighted least-squares problem in $\theta$ through the origin, solved by step 3. The averaged standard error is the Buckland–Burnham–Augustin form, which adds between-model spread to within-model variance.

## Sources

- H. Xue, X. Shen and W. Pan, *Constrained maximum likelihood-based Mendelian randomization robust to both correlated and uncorrelated pleiotropic effects*, Am. J. Hum. Genet. 108 (2021), 1251–1269, <https://doi.org/10.1016/j.ajhg.2021.05.014>, PMCID PMC8322939, Material and methods: Equation 5 (model averaging), Equations 6–7 (coordinate updates) and Equation 8 (Fisher information).
