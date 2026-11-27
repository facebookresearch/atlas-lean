# Capped log-sum estimate for damped influences

Let $E$ be a finite nonempty set, $0 < p < 1$, and $f = 1_A$ the indicator of a set $A \subseteq \{0, 1\}^E$. Write $\hat f(S)$, for $S \subseteq E$, for the [$p$-biased Fourier coefficients](../../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/pbiased-tensorize/ptn-coeff.md) of $f$, $\mathrm{Inf}_e = \mathbb{E}_p\lvert f(\omega^{e \to 1}) - f(\omega^{e \to 0})\rvert$ for the [influence](../../osss-inequality-for-decision-trees/infl.md) of $e \in E$ under the $p$-biased product measure $\mu_p$, $\delta = \max_{e \in E} \mathrm{Inf}_e$ and $I = \sum_{e \in E} \mathrm{Inf}_e$. Let $D_e(\rho)$ be the [damped influence](fsm2-damp-weight.md) of $e$. If $0 < \rho \le 1$, $1 \le q \le 2$, $\rho^2 = 4(q - 1)p(1-p)$, $I > 0$ and $0 < \delta < 1$, then

$$I \Big(\frac{2}{q} - 1\Big) \log \frac{1}{\delta} \le \sum_{e \in E,\ \mathrm{Inf}_e > 0} \mathrm{Inf}_e \log \frac{\mathrm{Inf}_e}{D_e(\rho)}.$$
