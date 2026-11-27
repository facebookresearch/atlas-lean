# Low-range residual case of the capped estimate

For a real number $q$, the low-range residual case for $q$ is the assertion that for every $p$ with $1/2 < p < q$ and $p < 1$, every finite nonempty set $E$, every indicator $f = 1_A$ of a set $A \subseteq \{0, 1\}^E$ with $\delta < e^{-1}$, and every $u \in (0, 1)$ such that

$$u < 1 - 4p(1-p) \quad \text{or} \quad \delta^{\frac{u}{2-u} - \left(\frac{2}{q^*(u)} - 1\right)} < 4p(1-p), \qquad q^*(u) = 1 + \frac{1 - u}{4p(1-p)},$$

the capped estimate holds:

$$\sum_{\emptyset \ne S \subseteq E} 4 \lvert S\rvert\, (1 - u)^{\lvert S\rvert - 1}\, \hat f(S)^2 \le \delta^{u/(2-u)}\, I.$$

Here $\hat f(S)$ are the [$p$-biased Fourier coefficients](../../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/pbiased-tensorize/ptn-coeff.md) of $f$, and $\delta = \max_e \mathrm{Inf}_e$ and $I = \sum_e \mathrm{Inf}_e$ are the maximal and total [influence](../../osss-inequality-for-decision-trees/infl.md) under the $p$-biased product measure. These are the $u$ below the hypercontractive range or failing the gap condition.
