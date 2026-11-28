# Location of every Cox maximizer

For survival data with observed times $T_i$, event indicators $\delta_i$ and covariate vectors $x_i \in \mathbb{R}^p$, let $U(\beta)$ be the Cox score vector and $I(\beta)$ the observed information matrix. If $\varepsilon > 0$ and $\langle U(\beta_0 + h), h\rangle < 0$ whenever $\|h\|_\infty = \varepsilon$, every global maximizer $\hat b$ of the log partial likelihood satisfies $\|\hat b - \beta_0\|_\infty < \varepsilon$.
