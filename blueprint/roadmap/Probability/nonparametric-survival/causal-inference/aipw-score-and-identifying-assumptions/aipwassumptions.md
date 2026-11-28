# Identifying assumptions for the AIPW estimator

Let $\mu$ be a measure on $\Omega$, $T \subseteq \Omega$ a treatment event, $X : \Omega \to \mathcal{X}$ a covariate with values in a measurable space, $Y$ the observed outcome and $Y_0, Y_1$ the potential outcomes. Write $\mathbb{E}[\,\cdot \mid X]$ for conditional expectation given $\sigma(X)$ and $\pi = \mathbb{E}[\mathbf{1}_T \mid X]$ for the true propensity. The identifying assumptions for the average treatment effect are:

- consistency: $Y = Y_1$ on $T$ and $Y = Y_0$ on $T^c$, at every point;
- mean exchangeability: $\mathbb{E}[\mathbf{1}_T Y_1 \mid X] = \pi\, \mathbb{E}[Y_1 \mid X]$ and $\mathbb{E}[\mathbf{1}_{T^c} Y_0 \mid X] = \mathbb{E}[\mathbf{1}_{T^c} \mid X]\, \mathbb{E}[Y_0 \mid X]$ $\mu$-a.e.;
- positivity (strong overlap): for some $\varepsilon > 0$, $\varepsilon \le \pi \le 1 - \varepsilon$ $\mu$-a.e.

Here $\mathbb{E}[f \mid X]$ is the conditional expectation given $\sigma(X)$ when $\sigma(X)$ is contained in the σ-algebra of $\Omega$, $\mu$ restricted to $\sigma(X)$ is σ-finite and $f$ is integrable, and it is $0$ otherwise; only in the first case is $\pi$ the actual propensity.
