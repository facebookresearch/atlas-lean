# LIML, GMM and structural mean model estimators of a causal effect

Let individuals $i = 1, \dots, N$ have exposure $x_i$, outcome $y_i$ and instruments $z_{i1}, \dots, z_{iK}$.

**Limited information maximum likelihood (Eq. 10).** In the model

$$x_i = \alpha_0 + \sum_k \alpha_k z_{ik} + \varepsilon_{Xi}, \qquad y_i = \beta_0 + \beta_1 x_i + \varepsilon_{Yi},$$

with $(\varepsilon_{Xi}, \varepsilon_{Yi})$ i.i.d. bivariate normal (their correlation encodes confounding), the LIML estimate of $\beta_1$ is the maximum likelihood estimate in this single-equation system. Equivalently it minimizes the variance ratio

$$\kappa(\beta) = \frac{(y - \beta x)^\top M_{1}(y - \beta x)}{(y - \beta x)^\top M_{Z}(y - \beta x)},$$

where $M_1$ and $M_Z$ are the residual-maker matrices of regression on a constant and on the instruments with a constant, respectively. So $\hat\beta_{\mathrm{LIML}}$ is the coefficient for which the instruments explain as little as possible of the "exposure-free" outcome $y - \beta x$.

**Generalized method of moments (Eqs. 14–17).** For a structural model $E(Y \mid \mathrm{do}(X = x)) = f(x; \beta)$, valid instruments give the population moment restrictions $E[Y - f(X; \beta)] = 0$ and $E[Z_k(Y - f(X; \beta))] = 0$ at the true $\beta$. In an exactly identified model (as many moment conditions as parameters, e.g. $K = 1$ with $\beta = (\beta_0, \beta_1)$ and a nonzero sample instrument–exposure covariance), the GMM estimate solves the sample equations $\sum_i (y_i - f(x_i; \beta)) = 0$ and $\sum_i z_{ik}(y_i - f(x_i; \beta)) = 0$ exactly. With $K > 1$ instruments the model is overidentified and these sample equations generally have no common solution, even for valid instruments (with one slope and two centred instruments they require the same slope to equal two sample covariance ratios); the GMM estimate instead minimizes the weighted moment norm

$$(y - f(x; \beta))^\top Z (Z^\top \Omega Z)^{-1} Z^\top (y - f(x; \beta)),$$

where $Z = (1, z_1, \dots, z_K)$. The estimate is consistent for any positive definite $\Omega$ and efficient for $\Omega_{ij} = \mathrm{cov}(\varepsilon_i, \varepsilon_j)$, which is estimated in two steps from first-step residuals. The continuously updating estimator lets $\Omega$ depend on $\beta$ during the minimization. It coincides with LIML under homoscedastic residuals.

**Structural mean models (Eqs. 18–19).** The linear SMM $E(Y(x) - Y(0) \mid X = x, Z = z) = \beta_1 x$, with $Y(0) \perp Z$, implies the population restrictions $E[(Z_k - E Z_k)(Y - \beta_1 X)] = 0$, $k = 1, \dots, K$. G-estimation uses the sample estimating functions

$$U_k(\beta_1) = \sum_i (z_{ik} - \bar z_k)(y_i - \beta_1 x_i), \qquad k = 1, \dots, K:$$

with $K = 1$ and $\sum_i (z_i - \bar z) x_i \ne 0$ it solves $U_1(\beta_1) = 0$ exactly, and with $K > 1$ it minimizes a weighted quadratic form $U(\beta_1)^\top W U(\beta_1)$ in $U = (U_1, \dots, U_K)$, as in GMM, since the $K$ equations generally have no common root.

**Single instrument.** With $K = 1$ and $\widehat{\mathrm{cov}}(z, x) \ne 0$, the linear GMM, linear SMM, LIML and two-stage least squares estimates all equal the ratio estimate $\hat\beta_{Y|Z}/\hat\beta_{X|Z}$.

## Remarks

With one instrument the moment conditions $\sum_i(y_i - \beta_0 - \beta_1 x_i) = 0$ and $\sum_i z_i(y_i - \beta_0 - \beta_1 x_i) = 0$ give $\sum_i (z_i - \bar z)(y_i - \beta_1 x_i) = 0$, so, when $\widehat{\mathrm{cov}}(z, x) \ne 0$, $\hat\beta_1 = \widehat{\mathrm{cov}}(z, y)/\widehat{\mathrm{cov}}(z, x)$, which is the ratio of the two regression slopes on $z$. This is literally the g-estimating equation, so the linear GMM and SMM estimates agree. LIML is exactly identified in this case: $\kappa(\beta) \ge 1$, and $\kappa = 1$ exactly when $y - \beta x$ is uncorrelated with $z$, which again gives the ratio. With several instruments the estimators are defined by minimization rather than by exact sample equations and differ in finite samples. 2SLS is biased toward the confounded association with weak instruments, while LIML has no finite moments but is close to median-unbiased. For a binary outcome the multiplicative (log-linear) GMM and SMM use the same equations with $f = \exp(\beta_0 + \beta_1 x)$ and multiplicative residuals $y_i/f - 1$. A logistic SMM cannot be estimated this way because of the non-collapsibility of the odds ratio.

## Depends on

- [Ratio estimate of a single SNP](ratio-estimate.md)

## Sources

- S. Burgess, D. S. Small and S. G. Thompson, "A review of instrumental variable estimators for Mendelian randomization", Statistical Methods in Medical Research (2015 online; 2017), Sections 5.1 (Equation (10)), 6.1 (Equations (14)–(17)), 6.2 and 6.3 (Equations (18)–(20)), <https://doi.org/10.1177/0962280215597579>, PMCID PMC5642006.
