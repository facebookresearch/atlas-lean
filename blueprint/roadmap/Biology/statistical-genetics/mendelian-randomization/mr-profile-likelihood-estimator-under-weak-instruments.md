# Profile-likelihood Mendelian randomization estimator under many weak instruments

**Setting.** For $p$ independent SNPs let $\hat\gamma_j \sim N(\gamma_j, \sigma_{Xj}^2)$ and
$\hat\Gamma_j \sim N(\Gamma_j, \sigma_{Yj}^2)$ be the exposure and outcome GWAS coefficients, with known variances and all
$2p$ estimates mutually independent (two-sample design). Assume no pleiotropy: $\Gamma_j = \beta_0 \gamma_j$ for every $j$.
Profiling the nuisance parameters $\gamma = (\gamma_1,\dots,\gamma_p)$ out of the Gaussian log-likelihood gives

$$\ell(\beta) = -\frac12 \sum_{j=1}^p \frac{(\hat\Gamma_j - \beta \hat\gamma_j)^2}{\sigma_{Xj}^2 \beta^2 + \sigma_{Yj}^2},$$

and the profile-likelihood (limited-information maximum likelihood) estimator is $\hat\beta = \arg\max_\beta \ell(\beta)$, a root of the profile score

$$\psi(\beta) = \sum_{j=1}^p \frac{(\hat\Gamma_j - \beta\hat\gamma_j)(\hat\Gamma_j \sigma_{Xj}^2 \beta + \hat\gamma_j \sigma_{Yj}^2)}{(\sigma_{Xj}^2\beta^2 + \sigma_{Yj}^2)^2}.$$

Let $n = \min(n_X, n_Y)$ and assume $\sigma_{Xj}^2, \sigma_{Yj}^2 \in [c/n, C/n]$ for constants $0 < c \le C$, and
$\|\gamma\|_2^2 = O(1)$. Define the average instrument strength $\kappa = \frac1p \sum_{j} \gamma_j^2/\sigma_{Xj}^2$.

**Theorem (consistency).** If $p/(n^2 \|\gamma\|_2^4) \to 0$ (equivalently $1/(p\kappa^2) \to 0$), then $\hat\beta \xrightarrow{p} \beta_0$.

**Theorem (asymptotic normality).** If in addition either $p \to \infty$ and $\|\gamma\|_3/\|\gamma\|_2 \to 0$, or $\kappa \to \infty$, then

$$\frac{V_2}{\sqrt{V_1}}(\hat\beta - \beta_0) \xrightarrow{d} N(0,1), \quad
V_1 = \sum_{j=1}^p \frac{\gamma_j^2 \sigma_{Yj}^2 + \Gamma_j^2 \sigma_{Xj}^2 + \sigma_{Xj}^2\sigma_{Yj}^2}{(\sigma_{Xj}^2\beta_0^2 + \sigma_{Yj}^2)^2}, \quad
V_2 = \sum_{j=1}^p \frac{\gamma_j^2 \sigma_{Yj}^2 + \Gamma_j^2 \sigma_{Xj}^2}{(\sigma_{Xj}^2\beta_0^2 + \sigma_{Yj}^2)^2}.$$

Since $V_1 = V_2 + \Theta(p)$ and $V_2 = \Theta(p\kappa)$, the profile likelihood is information unbiased iff $\kappa \to \infty$.

By contrast the [IVW estimator](ivw.md) satisfies $\hat\beta_{\mathrm{IVW}} \approx \beta_0 / (1 + 1/\kappa)$, so it is biased toward zero unless $\kappa \to \infty$.

## Depends on

- [Ratio estimate of a single SNP](ratio-estimate.md)
- [Inverse-variance-weighted estimator](ivw.md)

## Expansion

$\ell(\beta)$ is a weighted least-squares criterion for regressing $\hat\Gamma_j$ on $\hat\gamma_j$ through the origin, with the
variance of each residual $\hat\Gamma_j - \beta\hat\gamma_j$ equal to $\sigma_{Xj}^2\beta^2 + \sigma_{Yj}^2$; rewritten in terms of the
Wald ratios $\hat\beta_j = \hat\Gamma_j/\hat\gamma_j$ it is a generalized Cochran's $Q$. Each summand of $\psi$ has mean zero at
$\beta_0$, so consistency follows from a uniform law of large numbers driven by the total strength $p\kappa$, and normality from a
Taylor expansion $\hat\beta - \beta_0 \approx \psi(\beta_0)/V_2$ with $\operatorname{Var}\psi(\beta_0) = V_1$ and a Lyapunov CLT.
(Zhao et al. 2020, Equations 3.2–3.8, Theorems 3.1–3.2, Section 3.3.)

## Sources

- Q. Zhao, J. Wang, G. Hemani, J. Bowden, and D. S. Small, "Statistical inference in two-sample summary-data Mendelian randomization using robust adjusted profile score", The Annals of Statistics (2020), <https://doi.org/10.1214/19-aos1866>.
