# Capped estimate when the maximal influence is at least $e^{-1}$

Let $E$ be a finite nonempty set, $0 < p < 1$, and $f = 1_A$ the indicator of a set $A \subseteq \{0, 1\}^E$. Write $\hat f(S)$, for $S \subseteq E$, for the [$p$-biased Fourier coefficients](../../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/pbiased-tensorize/ptn-coeff.md) of $f$, $\mathrm{Inf}_e = \mathbb{E}_p\lvert f(\omega^{e \to 1}) - f(\omega^{e \to 0})\rvert$ for the [influence](../../osss-inequality-for-decision-trees/infl.md) of $e \in E$ under the $p$-biased product measure $\mu_p$, $\delta = \max_{e \in E} \mathrm{Inf}_e$ and $I = \sum_{e \in E} \mathrm{Inf}_e$. If $\delta \ge e^{-1}$, then for every $u \in (0, 1)$

$$\sum_{\emptyset \ne S \subseteq E} 4 \lvert S\rvert\, (1 - u)^{\lvert S\rvert - 1}\, \hat f(S)^2 \le \delta^{u/(2-u)}\, I.$$
