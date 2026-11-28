# Bias of Poisson autoregression under binomial under-reporting

**Model.** True case counts follow the stationary Poisson autoregression (a discrete-time transmission model when the disease is rare and the generation time is one step)

$$X_t \mid X_{t-1} \sim \mathrm{Pois}(\lambda_t), \qquad \lambda_t = \nu + \phi X_{t-1}, \qquad \nu > 0,\ 0 < \phi < 1,$$

with mean $\mu = \nu/(1 - \phi)$ and variance $\sigma^2 = \mu/(1 - \phi^2)$; here $\phi$ is a reproduction number and $\nu$ the endemic import rate. Reported cases are binomially thinned, $Y_t \mid X_t \sim \mathrm{Bin}(X_t, \pi)$ with reporting probability $0 < \pi \le 1$. Then $\tilde\mu = \mathbb{E}Y_t = \pi\mu$, $\tilde\sigma^2 = \operatorname{Var}Y_t = \pi^2\sigma^2 + \pi(1-\pi)\mu$, and the lag-one autocorrelation of $Y$ is

$$\tilde\rho(1) = \tilde\tau\,\phi, \qquad \tilde\tau = 1 - (1 - \pi)\frac{\tilde\mu}{\tilde\sigma^2} .$$

These moment equations give consistent estimators of $(\pi, \phi, \nu)$ from the reported series.

**Proposition (ignoring under-reporting).** Fit the Poisson autoregression to $y_1,\dots,y_T$ as if $\pi = 1$, with any consistent estimator. As $T \to \infty$:

1. $\hat\phi(\pi) \to \tilde\tau\phi < \phi$ for $\pi < 1$, and the limit increases with $\pi$: more severe under-reporting gives greater underestimation of the reproduction number.
2. $\hat\nu(\pi) \to (1 - \tilde\tau\phi)\dfrac{\pi\nu}{1 - \phi}$, where $\tilde\tau = \dfrac{\pi}{\pi + (1 - \pi)(1 - \phi^2)}$, and for $\pi < 1$ this limit exceeds the true $\nu$ if and only if

$$\phi^2 + \pi\phi > 1, \qquad \text{that is,} \qquad \phi > \frac{\sqrt{\pi^2 + 4} - \pi}{2} .$$

3. The derivative of the limit of $\hat\nu$ with respect to $\pi$ is negative if and only if

$$(1 - \phi)\Big(\frac{\pi}{1 - \phi^2}\Big)^2 + (2 - 2\pi - 2\phi + \phi\pi)\frac{\pi}{1 - \phi^2} + (1 - \pi)^2 < 0,$$

so for strongly transmissible diseases reporting fewer cases can increase the apparent endemic component (as $\pi \to 1$ the derivative tends to $(1 - \phi - \phi^2)\nu$, negative exactly when $\phi > (\sqrt5 - 1)/2$), while for $\phi < (\sqrt5 - 1)/2$ the limit of $\hat\nu$ is below $\nu$ and falls as reporting worsens, for every $\pi < 1$.

## Expansion

The naive fit is a Poisson autoregression, so its estimators converge to the parameters matching the mean and lag-one autocorrelation of $Y$: $\hat\phi \to \tilde\rho(1)$ and $\hat\nu \to \tilde\mu(1 - \tilde\rho(1))$. Thinning keeps the autocovariance structure but multiplies covariances by $\pi^2$ while adding binomial noise $\pi(1 - \pi)\mu$ to the variance, which attenuates the autocorrelation by $\tilde\tau = \pi^2\sigma^2/\tilde\sigma^2$. Substituting $\sigma^2 = \mu/(1 - \phi^2)$ gives $\tilde\tau = \pi/(\pi + (1 - \pi)(1 - \phi^2))$, and comparing with $\nu = \mu(1 - \phi)$ the limit exceeds $\nu$ iff $\pi(1 - \tilde\tau\phi) > 1 - \phi$; clearing denominators and dividing by $(1 - \pi)(1 - \phi) > 0$ reduces this to $\phi^2 + \pi\phi > 1$. For example, $\pi = 0.8$, $\phi = 0.5$ gives $\tilde\tau = 0.8/0.95$ and a limit of about $0.926\,\nu$, and as $\phi \to 0$ the limit tends to $\pi\nu < \nu$. Differentiating in $\pi$ gives the derivative condition. Appendix A.1 of the source (arXiv and published versions alike) expands $(1 - (1 - \phi)/\pi)(\pi/(1 - \phi^2) + 1 - \pi)$ with the sign of the last term $-(1 - \phi)(1 - \pi)/\pi$ flipped, which yields its square-root threshold, and Proposition 2 states the derivative condition with the inequality reversed; the statement above corrects both, and its conclusion is the reverse of the source's. The corrected threshold agrees with the source's Figure 1 ($\phi = 0.8$, where $\hat\nu$ is too high exactly for $\pi > 0.45$, that is, for $\pi$ close to 1).

## Sources

- Justin J Slater, Sindi G Bebeziqi, "Modelling under-reported data: pitfalls of naïve approaches and a new statistical framework for epidemic curve reconstruction", Journal of the Royal Statistical Society Series A: Statistics in Society (2026), qnag106, <https://doi.org/10.1093/jrsssa/qnag106>. Section 2 (Equations (1)–(3), Propositions 1 and 2) and Appendix A (A.1, A.2); Propositions 1 and 2 are stated there with the slips corrected on this page.
- Justin J. Slater, Sindi Bebeziqi, "Modelling Under-Reported Data: Pitfalls of Naïve Approaches and a New Statistical Framework for Epidemic Curve Reconstruction", arXiv (2025). Preprint of the article above, same propositions. Section 2 (Equations (hhh), (thinning), moment equations), Proposition 1, Proposition 2, Appendix A. <https://doi.org/10.48550/arXiv.2509.10668>
