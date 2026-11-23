# Capped estimate with zero weights holds trivially

Let $0 \le p \le 1$, let $E$ be a finite nonempty set and $f = 1_A$ the indicator of a set $A \subseteq \{0, 1\}^E$, with [$p$-biased Fourier coefficients](../../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/pbiased-tensorize/ptn-coeff.md) $\hat f(S)$; write $\mathrm{Inf}_e$ for the [influence](../../osss-inequality-for-decision-trees/infl.md) of $e$ under the $p$-biased product measure, $\delta = \max_e \mathrm{Inf}_e$ and $I = \sum_e \mathrm{Inf}_e$. For every real $u$,

$$\sum_{\emptyset \ne S \subseteq E} 0 \cdot \lvert S\rvert\, (1 - u)^{\lvert S\rvert - 1}\, \hat f(S)^2 \le \delta^{u/(2-u)}\, I$$

(with $u/(2 - u)$ read as $0$ at $u = 2$, and the real power $0^a$ read as $0$ for $a \ne 0$ and as $1$ for $a = 0$, which matters when $\delta = 0$): the left side is $0$ and the right side is nonnegative.
