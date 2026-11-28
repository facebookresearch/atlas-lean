# Spectral form of the PLEIO likelihood-ratio statistic

In the PLEIO model $\hat\eta_i \sim \mathrm{MVN}(0, \tau^2 \Omega + \Sigma)$ with $\Omega$ positive definite, let $\Omega^{-1/2} \Sigma\, \Omega^{-1/2} = P \Lambda P^{\mathsf T}$ with $P$ orthogonal and $\Lambda = \mathrm{diag}(\xi_1, \dots, \xi_T)$, $\xi_t > 0$, and set $y = P^{\mathsf T} \Omega^{-1/2} \hat\eta_i$. Then the coordinates $y_t$ are independent with $y_t \sim N(0, \xi_t + \tau^2)$, and the log-likelihood is

$$\ell(\tau^2) = -\frac12 \Bigl[ T \ln(2\pi) + \sum_{t=1}^T \ln(\xi_t + \tau^2) + \sum_{t=1}^T \frac{y_t^2}{\xi_t + \tau^2} \Bigr].$$

With $\hat\tau^2 = \arg\max_{\tau^2 \ge 0} \ell(\tau^2)$, the likelihood-ratio statistic $S = 2[\ell(\hat\tau^2) - \ell(0)]$ is

$$S_{\mathrm{PLEIO}} = \sum_{t=1}^T \ln\frac{\xi_t}{\xi_t + \hat\tau^2} + \sum_{t=1}^T \frac{y_t^2}{\xi_t} - \sum_{t=1}^T \frac{y_t^2}{\xi_t + \hat\tau^2}.$$

The first two derivatives of $\ell$ in $\tau^2$ are $-\frac12 \sum_t \bigl[(\xi_t + \tau^2)^{-1} - y_t^2 (\xi_t + \tau^2)^{-2}\bigr]$ and $\frac12 \sum_t \bigl[(\xi_t + \tau^2)^{-2} - 2 y_t^2 (\xi_t + \tau^2)^{-3}\bigr]$, so $\hat\tau^2$ is found by a one-dimensional Newton-Raphson search. Under $H_0$ the statistic is asymptotically a 50:50 mixture of $\chi^2_0$ and $\chi^2_1$, since the null value lies on the boundary of the parameter space.

## Depends on

- [PLEIO variance-component model for multi-trait summary statistics](pleio-variance-component-model.md)

## Expansion

The linear map $\Omega^{-1/2}$ turns the covariance into $\tau^2 I + \Omega^{-1/2}\Sigma\,\Omega^{-1/2}$, and the orthogonal $P^{\mathsf T}$ diagonalizes it without changing $\tau^2 I$; the Jacobian of the transformation does not depend on $\tau^2$, so likelihood ratios are unchanged. Each Newton step then costs $O(T)$ instead of inverting $\tau^2\Omega + \Sigma$. The source notes that the asymptotic boundary mixture is inaccurate for a small number of traits and that the exact null depends on $\Omega$ and $\Sigma$, so p-values are computed by mixture importance sampling (Step 4 of Material and methods).

## Sources

- C. H. Lee, H. Shi, B. Pasaniuc, E. Eskin and B. Han, PLEIO: a method to map and interpret pleiotropic loci with GWAS summary statistics, American Journal of Human Genetics 108 (2021), 36-48. <https://doi.org/10.1016/j.ajhg.2020.11.017> (PMCID PMC7820744)
