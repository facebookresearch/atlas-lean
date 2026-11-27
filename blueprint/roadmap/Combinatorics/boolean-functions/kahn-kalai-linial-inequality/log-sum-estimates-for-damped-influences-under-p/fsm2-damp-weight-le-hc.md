# Hypercontractive bound on the damped influence

Let $E$ be a finite set, $0 < p < 1$, and $f = 1_A$ the indicator of a set $A \subseteq \{0, 1\}^E$. Write $\hat f(S)$, for $S \subseteq E$, for the [$p$-biased Fourier coefficients](../../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/pbiased-tensorize/ptn-coeff.md) of $f$, $\mathrm{Inf}_e = \mathbb{E}_p\lvert f(\omega^{e \to 1}) - f(\omega^{e \to 0})\rvert$ for the [influence](../../osss-inequality-for-decision-trees/infl.md) of $e \in E$ under the $p$-biased product measure $\mu_p$ and $I = \sum_{e \in E} \mathrm{Inf}_e$. Let $D_e(\rho)$ be the [damped influence](fsm2-damp-weight.md) of $e$. If $0 \le \rho \le 1$, $1 \le q \le 2$ and $\rho^2 = 4(q - 1)p(1-p)$, then for every $e \in E$

$$D_e(\rho) \le \mathrm{Inf}_e^{2/q}.$$
