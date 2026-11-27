# Robust perfect adaptation from intein-charge conservation

**Setting.** A regulated network with species $X_1,\dots,X_L$ is in feedback with a controller network with species $Z_1,\dots,Z_M$; the controller acts only on the input species $X_1$ and senses only the regulated output $X_L$. Each controller species $Z_i$ contains $q_i^+$ active C-terminal and $q_i^-$ active N-terminal split-intein segments; set $q = (q_1^+ - q_1^-,\dots,q_M^+ - q_M^-)^\top$. The setpoint and sensing reactions are

$$\varnothing \xrightarrow{\ \mu_i + \theta_i x_L\ } Z_i\qquad (i = 1,\dots,M),$$

with $\mu = (\mu_i)$, $\theta = (\theta_i)$, at least one $\mu_i > 0$ and one $\theta_i > 0$, and all other controller reactions (splicing of complementary intein halves, binding, conversion, actuation of $X_1$) conserve the net charge $q^\top z$; there is no dilution of controller species.

**Theorem.** If the closed loop is stable (converges to a steady state), then

$$\lim_{t\to\infty} x_L(t) = -\frac{q^\top\mu}{q^\top\theta} > 0,$$

for every value of the regulated network's parameters and every constant disturbance. The integrated variable $z_I = q^\top z$ satisfies

$$z_I(t) = z_I(0) + \int_0^t \big(\mu_{\mathrm{eff}} - \theta_{\mathrm{eff}}\,x_L(\tau)\big)\,d\tau,\qquad \mu_{\mathrm{eff}} = q^\top\mu,\ \ \theta_{\mathrm{eff}} = -q^\top\theta.$$

In the stochastic setting, if the closed-loop Markov chain is ergodic, the stationary mean satisfies $\mathbb{E}_\pi[X_L] = -q^\top\mu/q^\top\theta$.

## Expansion

Because every reaction other than setpoint and sensing leaves $q^\top z$ unchanged, $\frac{d}{dt}q^\top z = q^\top\mu + (q^\top\theta)\,x_L$. At a steady state the left side is zero, which fixes $x_L$ independently of everything downstream; this is the integral-feedback mechanism behind [perfect adaptation](../../integral-feedback-and-perfect-adaptation/has-perfect-adaptation.md). The antithetic integral motif is the special case $\mu_1, \theta_2 > 0$, all other $\mu_i, \theta_j = 0$, and $q = (1,-1,\dots)^\top$, which gives the setpoint $\mu_1/\theta_2$. In the stochastic case the same identity holds for expectations of the reaction propensities, so ergodicity gives the stationary mean. With dilution of controller species the adaptation is no longer exact but remains close when dilution is slow compared with the controller reactions.

## Depends on

- [Perfect adaptation](../../integral-feedback-and-perfect-adaptation/has-perfect-adaptation.md)

## Sources

- Anastassov S, Filo M, Chang CH, Khammash M, "A cybergenetic framework for engineering intein-mediated integral feedback control systems", Nat Commun (2023), Theorem 1, Eqs. (1)–(3), Remarks 1.1–1.2 and Fig. 2, <https://doi.org/10.1038/s41467-023-36863-9>, PMCID PMC10008564.
