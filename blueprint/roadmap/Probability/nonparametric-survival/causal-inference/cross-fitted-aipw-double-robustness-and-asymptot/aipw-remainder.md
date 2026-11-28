# The AIPW remainder

Let $(\Omega, \mathcal{F}, \mu)$ be a measure space, $m$ a σ-algebra on $\Omega$ (the covariate information), $T \subseteq \Omega$ the treatment event and $Y_0, Y_1 : \Omega \to \mathbb{R}$ the potential outcomes. Write $e^* = \mu[\mathbf{1}_T \mid m]$ for the true propensity and $\mu_a^* = \mu[Y_a \mid m]$ for the true outcome regressions.

For real functions $e, g_0, g_1$ on $\Omega$ (candidate propensity and outcome regressions), the AIPW remainder is

$$R(e, g_0, g_1) = \int_\Omega \bigl(e^* - e\bigr)\left(\frac{\mu_1^* - g_1}{e} + \frac{\mu_0^* - g_0}{1 - e}\right) d\mu,$$

with the convention $x / 0 = 0$ and with the integral equal to $0$ when the integrand is not integrable. It is a product of the propensity error and the outcome-regression errors.

Here $\mu[f \mid m]$ is the conditional expectation of $f$ given $m$ when $m$ is contained in $\mathcal{F}$, $\mu$ restricted to $m$ is σ-finite and $f$ is integrable, and it is $0$ otherwise. Only in the first case are $e^*$ and $\mu_a^*$ the actual propensity and outcome regressions; the statement covers the other cases with these zero values.
