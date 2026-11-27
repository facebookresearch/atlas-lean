# Bias of Poisson autoregression under binomial under-reporting

**Model.** True case counts follow the stationary Poisson autoregression (a discrete-time transmission model when the disease is rare and the generation time is one step)

$$X_t \mid X_{t-1} \sim \mathrm{Pois}(\lambda_t), \qquad \lambda_t = \nu + \phi X_{t-1}, \qquad \nu > 0,\ 0 < \phi < 1,$$

with mean $\mu = \nu/(1 - \phi)$ and variance $\sigma^2 = \mu/(1 - \phi^2)$; here $\phi$ is a reproduction number and $\nu$ the endemic import rate. Reported cases are binomially thinned, $Y_t \mid X_t \sim \mathrm{Bin}(X_t, \pi)$ with reporting probability $0 < \pi \le 1$. Then $\tilde\mu = \mathbb{E}Y_t = \pi\mu$, $\tilde\sigma^2 = \operatorname{Var}Y_t = \pi^2\sigma^2 + \pi(1-\pi)\mu$, and the lag-one autocorrelation of $Y$ is

$$\tilde\rho(1) = \tilde\tau\,\phi, \qquad \tilde\tau = 1 - (1 - \pi)\frac{\tilde\mu}{\tilde\sigma^2} .$$

These moment equations give consistent estimators of $(\pi, \phi, \nu)$ from the reported series.

**Proposition (ignoring under-reporting).** Fit the Poisson autoregression to $y_1,\dots,y_T$ as if $\pi = 1$, with any consistent estimator. As $T \to \infty$:

1. $\hat\phi(\pi) \to \tilde\tau\phi < \phi$ for $\pi < 1$, and the limit increases with $\pi$: more severe under-reporting gives greater underestimation of the reproduction number.
2. $\hat\nu(\pi) \to (1 - \tilde\tau\phi)\dfrac{\pi\nu}{1 - \phi}$, and this limit exceeds the true $\nu$ if and only if

$$\phi < \sqrt{1 - \frac{1}{(1 - \pi) + 1/\pi}} .$$

3. The derivative of the limit of $\hat\nu$ with respect to $\pi$ is negative if and only if

$$(1 - \phi)\Big(\frac{\pi}{1 - \phi^2}\Big)^2 + (2 - 2\pi - 2\phi + \phi\pi)\frac{\pi}{1 - \phi^2} + (1 - \pi)^2 > 0,$$

so for weakly transmissible diseases reporting fewer cases can increase the apparent endemic component.

## Expansion

The naive fit is a Poisson autoregression, so its estimators converge to the parameters matching the mean and lag-one autocorrelation of $Y$: $\hat\phi \to \tilde\rho(1)$ and $\hat\nu \to \tilde\mu(1 - \tilde\rho(1))$. Thinning keeps the autocovariance structure but multiplies covariances by $\pi^2$ while adding binomial noise $\pi(1 - \pi)\mu$ to the variance, which attenuates the autocorrelation by $\tilde\tau = \pi^2\sigma^2/\tilde\sigma^2$. Substituting $\sigma^2 = \mu/(1 - \phi^2)$ and comparing with $\nu = \mu(1 - \phi)$ reduces the bias of $\hat\nu$ to a quadratic inequality in $\phi$, giving the threshold; differentiating in $\pi$ gives the derivative condition.

## Sources

- Justin J Slater, Sindi G Bebeziqi, "Modelling under-reported data: pitfalls of naïve approaches and a new statistical framework for epidemic curve reconstruction", Journal of the Royal Statistical Society Series A: Statistics in Society (2026), qnag106, <https://doi.org/10.1093/jrsssa/qnag106>. Published version of arXiv:2509.10668, cited next; locators there refer to the arXiv version.
- Justin J. Slater, Sindi Bebeziqi, "Modelling Under-Reported Data: Pitfalls of Naïve Approaches and a New Statistical Framework for Epidemic Curve Reconstruction", arXiv (2025). Section 2 (Equations (hhh), (thinning), moment equations), Proposition 1, Proposition 2, Appendix A. <https://doi.org/10.48550/arXiv.2509.10668>
