# Fourier total weight equals $4p(1-p)$ times the total influence

Let $E$ be a finite set, $0 < p < 1$, and $f = 1_A$ the indicator of a set $A \subseteq \{0, 1\}^E$. Write $\hat f(S)$, for $S \subseteq E$, for the [$p$-biased Fourier coefficients](../../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/pbiased-tensorize/ptn-coeff.md) of $f$, $\mathrm{Inf}_e = \mathbb{E}_p\lvert f(\omega^{e \to 1}) - f(\omega^{e \to 0})\rvert$ for the [influence](../../osss-inequality-for-decision-trees/infl.md) of $e \in E$ under the $p$-biased product measure $\mu_p$ and $I = \sum_{e \in E} \mathrm{Inf}_e$. Then

$$4 \sum_{S \subseteq E} \lvert S\rvert\, \hat f(S)^2 = 4p(1-p)\, I.$$
