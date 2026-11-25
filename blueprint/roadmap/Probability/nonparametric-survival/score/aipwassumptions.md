# AIPWAssumptions

Let $\mu$ be a measure on $\Omega$, $T \subseteq \Omega$ a treatment event, $X : \Omega \to \mathcal{X}$ a covariate with values in a measurable space, $Y$ the observed outcome and $Y_0, Y_1$ the potential outcomes. Write $\mathbb{E}[\,\cdot \mid X]$ for conditional expectation given $\sigma(X)$ and $\pi = \mathbb{E}[\mathbf{1}_T \mid X]$ for the true propensity. The identifying assumptions for the average treatment effect are:

- consistency: $Y = Y_1$ on $T$ and $Y = Y_0$ on $T^c$, at every point;
- mean exchangeability: $\mathbb{E}[\mathbf{1}_T Y_1 \mid X] = \pi\, \mathbb{E}[Y_1 \mid X]$ and $\mathbb{E}[\mathbf{1}_{T^c} Y_0 \mid X] = \mathbb{E}[\mathbf{1}_{T^c} \mid X]\, \mathbb{E}[Y_0 \mid X]$ $\mu$-a.e. (implied by $Y_a \perp T \mid X$);
- positivity (strong overlap): for some $\varepsilon > 0$, $\varepsilon \le \pi \le 1 - \varepsilon$ $\mu$-a.e.
