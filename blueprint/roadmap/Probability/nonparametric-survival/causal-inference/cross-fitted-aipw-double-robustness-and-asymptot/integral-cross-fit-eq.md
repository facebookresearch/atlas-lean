# Double robustness with sample-split nuisances

Let $(\Omega, \mathcal{F}, \mu)$ and $(\Omega_t, \mu_t)$ be probability spaces; a point $\omega_t \in \Omega_t$ is a training sample and $\omega \in \Omega$ an evaluation unit, with joint law $\mu_t \otimes \mu$. Let $m \subseteq \mathcal{F}$ be a sub-σ-algebra, $T \in \mathcal{F}$, and $Y, Y_0, Y_1 : \Omega \to \mathbb{R}$, with $e^* = \mu[\mathbf{1}_T \mid m]$ and $\mu_a^* = \mu[Y_a \mid m]$. For a measurable event $T$, an observed outcome $Y$ and real functions $e, g_0, g_1$, the AIPW score is $\psi(e, g_0, g_1) = g_1 - g_0 + \mathbf{1}_T (Y - g_1)/e - \mathbf{1}_{T^c} (Y - g_0)/(1 - e)$. Assume:

- consistency: $Y = \mathbf{1}_T Y_1 + \mathbf{1}_{T^c} Y_0$ $\mu$-a.e.;
- $Y_0, Y_1$ are integrable;
- mean exchangeability: $\mu[\mathbf{1}_T Y_1 \mid m] = e^* \mu_1^*$ and $\mu[\mathbf{1}_{T^c} Y_0 \mid m] = (1 - e^*)\mu_0^*$ $\mu$-a.e.;
- for every $\omega_t$, the fitted nuisances $\hat e(\omega_t), \hat g_0(\omega_t), \hat g_1(\omega_t) : \Omega \to \mathbb{R}$ are strongly $m$-measurable, $\hat g_0(\omega_t)$ and $\hat g_1(\omega_t)$ are $\mu$-integrable, and there is $\varepsilon(\omega_t) > 0$ with $\varepsilon(\omega_t) \le \hat e(\omega_t) \le 1 - \varepsilon(\omega_t)$ $\mu$-a.e.;
- $(\omega_t, \omega) \mapsto \psi(\hat e(\omega_t), \hat g_0(\omega_t), \hat g_1(\omega_t))(\omega)$ is integrable for $\mu_t \otimes \mu$.
- for $\mu_t$-almost every $\omega_t$, either $\hat e(\omega_t) = e^*$ $\mu$-a.e., or both $\hat g_0(\omega_t) = \mu_0^*$ and $\hat g_1(\omega_t) = \mu_1^*$ $\mu$-a.e.

Then the sample-split AIPW score is unbiased for the average treatment effect:

$$\int \psi(\hat e(\omega_t), \hat g_0(\omega_t), \hat g_1(\omega_t))(\omega)\, d(\mu_t \otimes \mu) = \int (Y_1 - Y_0)\, d\mu.$$

Which nuisance is correct may vary with the training sample.
