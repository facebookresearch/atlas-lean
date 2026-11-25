# The two-sided geometric mechanism is differentially private

Let $f : D \to \mathbb{Z}$ and $\varepsilon > 0$. If $|f(d) - f(d')| \le 1$ whenever $\mathrm{adj}(d, d')$, then the [two-sided geometric mechanism](geom-mech.md) for $f$ with parameter $\varepsilon$ is [$\varepsilon$-differentially private](../differential-privacy/is-dp.md) for $\mathrm{adj}$.

## Sources

- A. Ghosh, T. Roughgarden and M. Sundararajan, *Universally Utility-Maximizing Privacy Mechanisms*, STOC 2009 (the two-sided geometric distribution).
