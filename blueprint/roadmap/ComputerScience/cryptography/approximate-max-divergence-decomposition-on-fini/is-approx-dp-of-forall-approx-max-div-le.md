# Approximate max-divergence bounds give approximate differential privacy

Let $M$ be a mechanism with values in probability mass functions on a finite nonempty type and $\varepsilon \ge 0$, $\delta \ge 0$. If $D_\infty^\delta(M(d) \| M(d')) \le \varepsilon$ ([approximate max-divergence bound](approx-max-div-le.md)) for every ordered pair with $\mathrm{adj}(d, d')$, then $M$ is [$(\varepsilon, \delta)$-differentially private](../approximate-differential-privacy/is-approx-dp.md) for $\mathrm{adj}$.
