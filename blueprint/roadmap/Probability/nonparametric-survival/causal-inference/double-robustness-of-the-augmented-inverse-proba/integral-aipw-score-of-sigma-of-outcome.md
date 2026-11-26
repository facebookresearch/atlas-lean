# Double robustness, outcome regressions correct

Let $(\Omega, \mathcal{F}, \mu)$ be a finite measure space, $m \subseteq \mathcal{F}$ a sub-σ-algebra, $T \in \mathcal{F}$, and $Y, Y_0, Y_1 : \Omega \to \mathbb{R}$. Write $e^* = \mu[\mathbf{1}_T \mid m]$ and $\mu_a^* = \mu[Y_a \mid m]$, and let $\psi(e, g_0, g_1) = g_1 - g_0 + \mathbf{1}_T (Y - g_1)/e - \mathbf{1}_{T^c} (Y - g_0)/(1 - e)$ be the AIPW score. Assume

- consistency: $Y = \mathbf{1}_T Y_1 + \mathbf{1}_{T^c} Y_0$ $\mu$-a.e.;
- $Y_0, Y_1$ are integrable;
- mean exchangeability: $\mu[\mathbf{1}_T Y_1 \mid m] = e^* \mu_1^*$ and $\mu[\mathbf{1}_{T^c} Y_0 \mid m] = (1 - e^*) \mu_0^*$ $\mu$-a.e.;
- the candidates $e, g_0, g_1$ are strongly $m$-measurable, $g_0, g_1$ are integrable, and $\varepsilon \le e \le 1 - \varepsilon$ $\mu$-a.e. for some $\varepsilon > 0$;
- both outcome regressions are correct: $g_0 = \mu_0^*$ and $g_1 = \mu_1^*$ $\mu$-a.e.

Then, for any such propensity $e$, the integral of the score equals the integral of the treatment-effect contrast:

$$\int_\Omega \psi(e, g_0, g_1)\, d\mu = \int_\Omega (Y_1 - Y_0)\, d\mu.$$

When $\mu$ is a probability measure, this says that the score is unbiased for the average treatment effect.

The true propensity $e^*$ may reach $0$ or $1$ here.
