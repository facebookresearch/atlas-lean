# Capped estimate at the endpoint $u = 1$

Let $E$ be a finite nonempty set, $0 < p < 1$, and $f = 1_A$ the indicator of a set $A \subseteq \{0, 1\}^E$. Write $\hat f(S)$, for $S \subseteq E$, for the [$p$-biased Fourier coefficients](../../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/pbiased-tensorize/ptn-coeff.md) of $f$, $\mathrm{Inf}_e = \mathbb{E}_p\lvert f(\omega^{e \to 1}) - f(\omega^{e \to 0})\rvert$ for the [influence](../../osss-inequality-for-decision-trees/infl.md) of $e \in E$ under the $p$-biased product measure $\mu_p$, $\delta = \max_{e \in E} \mathrm{Inf}_e$ and $I = \sum_{e \in E} \mathrm{Inf}_e$. At $u = 1$ the capped estimate holds:

$$\sum_{\emptyset \ne S \subseteq E} 4 \lvert S\rvert\, (1 - 1)^{\lvert S\rvert - 1}\, \hat f(S)^2 \le \delta^{1/(2-1)}\, I = \delta\, I,$$

where $0^0 = 1$, so the left side is $4 \sum_{e \in E} \hat f(\{e\})^2$.
