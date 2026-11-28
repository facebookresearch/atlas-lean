# Sample size for a one-sided z test

Let $\alpha, \beta \in (0, \tfrac12)$, $\delta > 0$, $v > 0$ and $\mu_0 \in \mathbb{R}$, write $\Phi$ for the standard normal distribution function, $\Phi^{-1}$ for its quantile function, $z_\alpha = \Phi^{-1}(1 - \alpha)$ and $z_\beta = \Phi^{-1}(1 - \beta)$. If

$$n \ge \Big\lceil \Big(\frac{\sqrt v\,(z_\alpha + z_\beta)}{\delta}\Big)^2 \Big\rceil,$$

then the one-sided z test that rejects when $\sqrt n\,(\bar x - \mu_0)/\sqrt v > z_\alpha$ has power at least $1 - \beta$ against the mean $\mu_0 + \delta$: the rejection region has probability at least $1 - \beta$ under $\mathcal N(\mu_0 + \delta, v)^{\otimes n}$, the law of an i.i.d. normal sample of size $n$.
