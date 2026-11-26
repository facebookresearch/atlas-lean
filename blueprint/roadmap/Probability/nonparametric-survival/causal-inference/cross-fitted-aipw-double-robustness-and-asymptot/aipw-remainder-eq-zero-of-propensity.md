# The AIPW remainder vanishes when the propensity is correct

Let $(\Omega, \mathcal{F}, \mu)$ be a measure space, $m$ a σ-algebra on $\Omega$ (the covariate information), $T \subseteq \Omega$ the treatment event and $Y_0, Y_1 : \Omega \to \mathbb{R}$ the potential outcomes. Write $e^* = \mu[\mathbf{1}_T \mid m]$ for the true propensity and $\mu_a^* = \mu[Y_a \mid m]$ for the true outcome regressions.

If the candidate propensity is correct, $e = e^*$ $\mu$-almost everywhere, then for all real functions $g_0, g_1$ the AIPW remainder vanishes:

$$R(e, g_0, g_1) = \int_\Omega (e^* - e)\left(\frac{\mu_1^* - g_1}{e} + \frac{\mu_0^* - g_0}{1 - e}\right) d\mu = 0,$$

with $x / 0 = 0$ and the integral equal to $0$ when the integrand is not integrable.

Here $\mu[f \mid m]$ is the conditional expectation of $f$ given $m$ when $m$ is contained in $\mathcal{F}$, $\mu$ restricted to $m$ is σ-finite and $f$ is integrable, and it is $0$ otherwise. Only in the first case are $e^*$ and $\mu_a^*$ the actual propensity and outcome regressions; the statement covers the other cases with these zero values.
