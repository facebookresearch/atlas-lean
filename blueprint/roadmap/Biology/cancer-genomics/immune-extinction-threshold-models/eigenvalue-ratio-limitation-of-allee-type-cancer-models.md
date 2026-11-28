# Eigenvalue-ratio limitation of Allee-type cancer models

**Setting.** Let $x(t) \ge 0$ be the number of cancer cells. Richards' model $\dot x = \nu r x\bigl(1 - (x/K)^{1/\nu}\bigr)$ has an unstable extinction state with growth rate $\lambda_{\mathrm{grow}} = \nu r$ and a stable carrying capacity $K$ with saturation rate $-\lambda_{\mathrm{sat}} = r$, so $|\lambda_{\mathrm{grow}}/\lambda_{\mathrm{sat}}| = \nu$; typical cancer progression (fast early growth, slower saturation) requires $|\lambda_{\mathrm{grow}}/\lambda_{\mathrm{sat}}| \ge 1$, i.e. $\nu \ge 1$ ($\nu = 1$ logistic, $\nu \to \infty$ Gompertz). To represent immune control, the generalized Allee model

$$\dot x = -\nu^2 r\, x\Bigl(1 - \bigl(\tfrac{x}{A}\bigr)^{1/\nu}\Bigr)\Bigl(1 - \bigl(\tfrac{x}{K}\bigr)^{1/\nu}\Bigr), \qquad 0 < A < K,$$

adds an extinction threshold $A$ (the immune response): $x = 0$ and $x = K$ are stable and $x = A$ is unstable.

**Proposition.** In the generalized Allee model the linearisation rates are

$$\lambda_A = \nu r\bigl(1 - (A/K)^{1/\nu}\bigr) > 0, \qquad \lambda_K = -\nu r\bigl((K/A)^{1/\nu} - 1\bigr) < 0,$$

so the ratio of growth just above the threshold to saturation near $K$ is

$$\Bigl|\frac{\lambda_A}{\lambda_K}\Bigr| = \Bigl(\frac{A}{K}\Bigr)^{1/\nu} < 1$$

for every shape parameter $\nu > 0$: a fixed immune threshold cannot reproduce the fast-escape, slow-saturation shape of observed cancer progression. The remedy proposed is to let stem-cell mutations enter at an age-dependent rate and let the immune threshold $A(t)$ move in time (weakening immunity), so that the population can cross a moving extinction threshold and then grow as in Richards' model.

## Expansion

The formulas follow by differentiating the right-hand side at $x = A$ and $x = K$: only the factor that vanishes contributes, with derivative $-1/(\nu A)$ or $-1/(\nu K)$ respectively, and the ratio simplifies because $(1 - a)/(a^{-1} - 1) = a$ for $a = (A/K)^{1/\nu}$. With a moving threshold the escape from immune control is a rate-dependent (tipping-like) event rather than a fixed-threshold crossing, and the model then reproduces age-incidence and progression data for real cancers.

## Sources

- F. Bastian, H. Alkhayuon, K. Mulchrone, M. O'Riordain, "Cancer model with moving extinction threshold reproduces real cancer data", *Journal of The Royal Society Interface* 22(231) (2025), 20240844, Richards' model and the generalized Allee model (Model 1) with their linear stability analysis, <https://doi.org/10.1098/rsif.2024.0844> (preprint arXiv:2506.05992).
