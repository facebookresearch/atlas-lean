# Adjusted profile score for Mendelian randomization with systematic pleiotropy

**Model.** In the two-sample summary-data setting of the
[profile-likelihood estimator](mr-profile-likelihood-estimator-under-weak-instruments.md), allow pleiotropic direct effects
$\alpha_j = \Gamma_j - \beta_0\gamma_j \overset{\text{iid}}{\sim} N(0, \tau_0^2)$, so that

$$\hat\Gamma_j \sim N(\gamma_j \beta_0,\ \sigma_{Yj}^2 + \tau_0^2), \qquad \hat\gamma_j \sim N(\gamma_j, \sigma_{Xj}^2), \qquad j = 1, \dots, p.$$

The profile score in $\tau^2$ of the profile likelihood is biased, so the maximum likelihood estimator is inconsistent. The
**adjusted profile score** (APS) is $\psi = (\psi_1, \psi_2)$ with

$$\psi_1(\beta,\tau^2) = \sum_{j=1}^p \frac{(\hat\Gamma_j - \beta\hat\gamma_j)\bigl(\hat\Gamma_j \sigma_{Xj}^2 \beta + \hat\gamma_j(\sigma_{Yj}^2 + \tau^2)\bigr)}{(\sigma_{Xj}^2\beta^2 + \sigma_{Yj}^2 + \tau^2)^2},$$

$$\psi_2(\beta,\tau^2) = \sum_{j=1}^p \sigma_{Xj}^2\, \frac{(\hat\Gamma_j - \beta\hat\gamma_j)^2 - (\sigma_{Xj}^2\beta^2 + \sigma_{Yj}^2 + \tau^2)}{(\sigma_{Xj}^2\beta^2 + \sigma_{Yj}^2 + \tau^2)^2},$$

and the APS estimator $(\hat\beta, \hat\tau^2)$ is a nontrivial finite root of $\psi(\beta,\tau^2) = 0$. Every summand of $\psi_1$ and
$\psi_2$ has mean zero at $(\beta_0, \tau_0^2)$.

**Theorem.** Assume the Gaussian summary-data model with known variances, $\sigma_{Xj}^2, \sigma_{Yj}^2 = \Theta(1/n)$ with
$n = \min(n_X, n_Y)$, $(\beta_0, p\tau_0^2)$ in the interior of a bounded set $B \subset \mathbb{R} \times \mathbb{R}_+$,
$\|\gamma\|_2^2 = \Theta(1)$, $p \to \infty$ and $p/n^2 \to 0$. Then with probability tending to one the APS equations have a
solution with $(\hat\beta, p\hat\tau^2) \in B$, and every solution in $B$ satisfies $\hat\beta \xrightarrow{p} \beta_0$ and
$p\hat\tau^2 - p\tau_0^2 \xrightarrow{p} 0$.

## Depends on

- [Profile-likelihood Mendelian randomization estimator under many weak instruments](mr-profile-likelihood-estimator-under-weak-instruments.md)

## Expansion

The profile score in $\tau^2$ weights the squared residual by $(\sigma_{Xj}^2\beta^2+\sigma_{Yj}^2+\tau^2)^{-2}$ but subtracts
$(\sigma_{Yj}^2+\tau^2)^{-1}$, whose mismatch leaves a nonzero mean. Replacing it with the residual variance itself, following
McCullagh and Tibshirani's score adjustment, makes each summand an unbiased estimating function; the $\sigma_{Xj}^2$ weight is used
in the consistency proof. Because the denominators have higher degree than the numerators, $\psi \to 0$ as $|\beta| \to \infty$
or $\tau^2 \to \infty$, which is why consistency is stated for roots in a bounded set. Replacing the squared loss by a robust loss
(Huber or Tukey) gives the robust APS (RAPS) for idiosyncratic outlying pleiotropy. (Zhao et al. 2020, Model 2, Equations 4.1–4.3,
Assumptions 4–5 and Theorem 4.1.)

## Sources

- Q. Zhao, J. Wang, G. Hemani, J. Bowden, and D. S. Small, "Statistical inference in two-sample summary-data Mendelian randomization using robust adjusted profile score", The Annals of Statistics (2020), <https://doi.org/10.1214/19-aos1866>.
