# Log-sum inequality for influences against damped influences

Let $E$ be a finite set, $0 < p < 1$, and $f = 1_A$ the indicator of a set $A \subseteq \{0, 1\}^E$. Write $\hat f(S)$, for $S \subseteq E$, for the [$p$-biased Fourier coefficients](../../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/pbiased-tensorize/ptn-coeff.md) of $f$, $\mathrm{Inf}_e = \mathbb{E}_p\lvert f(\omega^{e \to 1}) - f(\omega^{e \to 0})\rvert$ for the [influence](../../osss-inequality-for-decision-trees/infl.md) of $e \in E$ under the $p$-biased product measure $\mu_p$ and $I = \sum_{e \in E} \mathrm{Inf}_e$. Let $D_e(\rho)$ be the [damped influence](fsm2-damp-weight.md) of $e$, and let $P = \{e \in E : \mathrm{Inf}_e > 0\}$. If $0 < \rho \le 1$, $1 \le q \le 2$, $\rho^2 = 4(q - 1)p(1-p)$ and $\sum_{e \in P} \mathrm{Inf}_e > 0$, then

$$\Big(\sum_{e \in P} \mathrm{Inf}_e\Big) \log \frac{\sum_{e \in P} \mathrm{Inf}_e}{\sum_{e \in P} D_e(\rho)} \le \sum_{e \in P} \mathrm{Inf}_e \log \frac{\mathrm{Inf}_e}{D_e(\rho)}.$$

This is the log-sum inequality for the influences against the damped influences.
