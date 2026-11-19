# Damped total weight at $u = 0$ is at most the total influence

Let $E$ be a finite set, $0 < p < 1$, and $f = 1_A$ the indicator of a set $A \subseteq \{0, 1\}^E$. Write $\hat f(S)$, for $S \subseteq E$, for the [$p$-biased Fourier coefficients](../../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/pbiased-tensorize/ptn-coeff.md) of $f$, $\mathrm{Inf}_e = \mathbb{E}_p\lvert f(\omega^{e \to 1}) - f(\omega^{e \to 0})\rvert$ for the [influence](../../osss-inequality-for-decision-trees/infl.md) of $e \in E$ under the $p$-biased product measure $\mu_p$ and $I = \sum_{e \in E} \mathrm{Inf}_e$. At $u = 0$ the damped total weight is at most the total influence:

$$\sum_{\emptyset \ne S \subseteq E} 4 \lvert S\rvert\, (1 - 0)^{\lvert S\rvert - 1}\, \hat f(S)^2 \le I.$$
