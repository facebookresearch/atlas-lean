# Aipw Remainder

Let $(\Omega, \mathcal{F}, \mu)$ be a measure space, $m$ a σ-algebra on $\Omega$ (the covariate information), $T \subseteq \Omega$ the treatment event and $Y_0, Y_1 : \Omega \to \mathbb{R}$ the potential outcomes. Write $e^* = \mu[\mathbf{1}_T \mid m]$ for the true propensity and $\mu_a^* = \mu[Y_a \mid m]$ for the true outcome regressions.

For real functions $e, g_0, g_1$ on $\Omega$ (candidate propensity and outcome regressions), the AIPW remainder is

$$R(e, g_0, g_1) = \int_\Omega \bigl(e^* - e\bigr)\left(\frac{\mu_1^* - g_1}{e} + \frac{\mu_0^* - g_0}{1 - e}\right) d\mu,$$

with the convention $x / 0 = 0$ and with the integral equal to $0$ when the integrand is not integrable. It is a product of the propensity error and the outcome-regression errors; under the hypotheses of the exact-bias identity for the AIPW score it equals the bias $\mathbb{E}[\psi(e, g_0, g_1)] - \mathbb{E}[Y_1 - Y_0]$ of that score.
