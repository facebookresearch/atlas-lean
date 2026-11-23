# Damped total weight as a sum of per-coordinate weights

Let $E$ be a finite set, $0 < p < 1$, and $f = 1_A$ the indicator of a set $A \subseteq \{0, 1\}^E$. Write $\hat f(S)$, for $S \subseteq E$, for the [$p$-biased Fourier coefficients](../../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/pbiased-tensorize/ptn-coeff.md) of $f$, $\mathrm{Inf}_e = \mathbb{E}_p\lvert f(\omega^{e \to 1}) - f(\omega^{e \to 0})\rvert$ for the [influence](../../osss-inequality-for-decision-trees/infl.md) of $e \in E$ under the $p$-biased product measure $\mu_p$ and $I = \sum_{e \in E} \mathrm{Inf}_e$. For every $u \in [0, 1]$,

$$\sum_{\emptyset \ne S \subseteq E} 4 \lvert S\rvert\, (1 - u)^{\lvert S\rvert - 1}\, \hat f(S)^2 = 4p(1-p) \sum_{e \in E} D_e(u),$$

where $D_e(u) = \sum_{S \ni e} (1 - u)^{\lvert S\rvert - 1} \big(\hat f(S)/\sqrt{p(1-p)}\big)^2$ is the [per-coordinate damped weight](frh-per-coord-weight.md).
