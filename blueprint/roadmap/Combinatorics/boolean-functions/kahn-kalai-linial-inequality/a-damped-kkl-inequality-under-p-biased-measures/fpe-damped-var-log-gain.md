# Damped KKL inequality under the $p$-biased measure

Let $E$ be a finite nonempty set, $0 < p < 1$, and $f = 1_A$ the indicator of a set $A \subseteq \{0, 1\}^E$. Write $\hat f(S)$, for $S \subseteq E$, for the [$p$-biased Fourier coefficients](../../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/pbiased-tensorize/ptn-coeff.md) of $f$, $\mathrm{Inf}_e = \mathbb{E}_p\lvert f(\omega^{e \to 1}) - f(\omega^{e \to 0})\rvert$ for the [influence](../../osss-inequality-for-decision-trees/infl.md) of $e \in E$ under the $p$-biased product measure $\mu_p$, $\delta = \max_{e \in E} \mathrm{Inf}_e$ and $I = \sum_{e \in E} \mathrm{Inf}_e$. With $A = 4p(1-p)$,

$$2 \Big(\sum_{\emptyset \ne S \subseteq E} \frac{A^{\lvert S\rvert - 1}}{A}\, \hat f(S)^2\Big) \log \frac{1}{\delta} \le I$$

(with $\log(1/\delta)$ read as $0$ when $\delta = 0$).
