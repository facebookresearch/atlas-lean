# SEIR model with psychological incidence and sliding-mode control of exposure

**Model.** With population fractions $S, E, I, R$ summing to $1$, birth and death rate $\mu$, latency exit rate $\sigma$, recovery rate $\gamma$, contact rate $\beta_0$ and intervention strength $\alpha \ge 0$,

$$\dot S = \mu - \frac{\beta_0 S I}{1 + \alpha I^2} - \mu S, \qquad \dot E = \frac{\beta_0 S I}{1 + \alpha I^2} - (\sigma + \mu) E, \qquad \dot I = \sigma E - (\gamma + \mu) I,$$

on the invariant region $\{S, E, I \ge 0,\ S + E + I \le 1\}$. The incidence is non-monotone in $I$: it increases for $I < \alpha^{-1/2}$ and decreases beyond.

**Threshold.** The disease-free equilibrium $(1, 0, 0)$ has characteristic polynomial $(\lambda + \mu)\big[\lambda^2 + (2\mu + \gamma + \sigma)\lambda + (\mu + \sigma)(\mu + \gamma)(1 - \mathcal{R}_0)\big]$ with

$$\mathcal{R}_0 = \frac{\sigma\beta_0}{(\mu + \sigma)(\mu + \gamma)},$$

independent of $\alpha$; it is locally asymptotically stable for $\mathcal{R}_0 < 1$ and unstable for $\mathcal{R}_0 > 1$.

**Endemic equilibrium.** For $\mathcal{R}_0 > 1$ there is a unique endemic equilibrium, with $E^* = (\gamma + \mu)I^*/\sigma$, $S^* = (1 + \alpha I^{*2})/\mathcal{R}_0$, and $I^*$ the positive root of

$$\alpha I^2 + \frac{\beta_0}{\mu} I - (\mathcal{R}_0 - 1) = 0, \qquad I^* = \frac{-\beta_0/\mu + \sqrt{\beta_0^2/\mu^2 + 4\alpha(\mathcal{R}_0 - 1)}}{2\alpha} \quad (\alpha > 0);$$

for $\mathcal{R}_0 < 1$ no positive root exists. $I^*$ decreases as $\alpha$ increases.

**Sliding-mode control.** To hold the exposed fraction at a target $E_d$, take the sliding variable $\varsigma = \Lambda(E - E_d)$, $\Lambda > 0$, and the constant-rate reaching law $\dot\varsigma = -\kappa\,\mathrm{sign}(\varsigma)$. Solving $\Lambda\big(\beta_0 SI/(1 + \alpha I^2) - (\sigma + \mu)E\big) = -\kappa\,\mathrm{sign}(\varsigma)$ for the control gives

$$\alpha = \frac{1}{I^2}\left[\frac{\beta_0 S I}{(\sigma + \mu)E - (\kappa/\Lambda)\,\mathrm{sign}(\varsigma)} - 1\right].$$

If the $E$-equation carries a disturbance $\epsilon(t)$ with $|\epsilon| \le \phi$, then $V = \tfrac12\varsigma^2$ satisfies $\dot V \le -|\varsigma|(\kappa - \phi)$ (with $\Lambda = 1$), so for $\kappa > \phi$ the sliding surface $E = E_d$ is reached in finite time, at most $|\varsigma(0)|/(\kappa - \phi)$.

## Expansion

Near the disease-free state $1 + \alpha I^2 \approx 1$, so the behavioural response does not enter the linearization; this is why $\mathcal{R}_0$ is the classical SEIR value $\beta_0 \cdot \frac{\sigma}{\sigma + \mu}\cdot\frac{1}{\gamma + \mu}$. The quadratic for $I^*$ comes from substituting $E^*$ and $S^*$ into $\dot S = 0$, giving $\mu(\mathcal{R}_0 - 1 - \alpha I^2) = \beta_0 I$; its constant term is negative exactly when $\mathcal{R}_0 > 1$ and its coefficients are otherwise positive, so Descartes' rule gives a unique positive root. The control law inverts the incidence term for $\alpha$, so that exposure obeys the prescribed reaching dynamics; physically it relaxes restrictions when $E$ is below target and tightens them when above, and the sign term confers robustness to bounded model error at the cost of chattering.

## Sources

- G. Rohith, K. B. Devika, "Dynamics and control of COVID-19 pandemic with nonlinear incidence rates", Nonlinear Dynamics 101 (2020) 2013–2026, Section 2 (model (2)–(6), characteristic equation (8), $\mathcal{R}_0$ (10), Theorems 1–2 and equations (12)–(14)) and Section 4 (sliding surface, reaching law (19), control law (23), Lyapunov analysis (24)–(33)), <https://doi.org/10.1007/s11071-020-05774-5>.
