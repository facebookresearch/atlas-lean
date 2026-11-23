# Covariance form of the Poincaré inequality

Let $E$ be a finite set, $\nu$ a [product probability weight](is-prob-weight.md) on $\{0, 1\}^E$, $f = 1_A$ the indicator of a set $A \subseteq \{0, 1\}^E$ and $g : \{0, 1\}^E \to \mathbb{R}$. Then

$$\mathrm{Cov}_\nu(f, g) \le \sum_{e \in E} \mathrm{Inf}_e(g),$$

with $\mathrm{Inf}_e(g) = \mathbb{E}_\nu\lvert g(\omega^{e \to 1}) - g(\omega^{e \to 0})\rvert$ the [influence](infl.md) under $\nu$.
