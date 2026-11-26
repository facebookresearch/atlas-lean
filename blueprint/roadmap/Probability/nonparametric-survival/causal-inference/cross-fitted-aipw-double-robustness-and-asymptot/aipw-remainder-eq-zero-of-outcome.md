# Aipw Remainder eq zero of outcome

Let $(\Omega, \mathcal{F}, \mu)$ be a measure space, $m$ a σ-algebra on $\Omega$ (the covariate information), $T \subseteq \Omega$ the treatment event and $Y_0, Y_1 : \Omega \to \mathbb{R}$ the potential outcomes. Write $e^* = \mu[\mathbf{1}_T \mid m]$ for the true propensity and $\mu_a^* = \mu[Y_a \mid m]$ for the true outcome regressions.

If both candidate outcome regressions are correct, $g_0 = \mu_0^*$ and $g_1 = \mu_1^*$ $\mu$-almost everywhere, then for every real function $e$ the AIPW remainder vanishes:

$$R(e, g_0, g_1) = \int_\Omega (e^* - e)\left(\frac{\mu_1^* - g_1}{e} + \frac{\mu_0^* - g_0}{1 - e}\right) d\mu = 0.$$
