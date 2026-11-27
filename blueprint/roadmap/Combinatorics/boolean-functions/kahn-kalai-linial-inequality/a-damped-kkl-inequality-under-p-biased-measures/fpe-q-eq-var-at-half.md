# Damped variance equals the variance at $p = 1/2$

Let $E$ be a finite set, $f = 1_A$ the indicator of a set $A \subseteq \{0, 1\}^E$, and $\hat f(S)$ the [$p$-biased Fourier coefficients](../../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/pbiased-tensorize/ptn-coeff.md) of $f$ at $p = 1/2$. At $p = 1/2$, where $4p(1-p) = 1$, the damped variance equals the variance under the uniform measure:

$$\sum_{\emptyset \ne S \subseteq E} \frac{1^{\lvert S\rvert - 1}}{1}\, \hat f(S)^2 = \sum_{\emptyset \ne S \subseteq E} \hat f(S)^2 = \mathrm{Var}(f).$$
