# Summed per-coordinate Bonami–Beckner bound

Let $E$ be a finite set and $f = 1_A$ the indicator of a set $A \subseteq \{0, 1\}^E$, with Walsh–Fourier coefficients $\hat f(S)$ under the uniform measure and [influence](../../osss-inequality-for-decision-trees/infl.md) $\mathrm{Inf}_e$. For every $\rho \in [0, 1]$,

$$\sum_{\emptyset \ne S \subseteq E} \lvert S\rvert\, \rho^{2(\lvert S\rvert - 1)} \cdot 4 \hat f(S)^2 \le \sum_{e \in E} \mathrm{Inf}_e^{2/(1 + \rho^2)}.$$

This is the [per-coordinate Bonami–Beckner bound](bph-per-coord-hc.md) summed over $e \in E$.
