# Low-degree residual case of the capped estimate

For a real number $q$, the low-degree residual case for $q$ is the assertion that for every $p$ with $1/2 < p < q$ and $p < 1$, every finite nonempty set $E$, every indicator $f = 1_A$ of a set $A \subseteq \{0, 1\}^E$ with $\delta < e^{-1}$, and every $u \in (0, 1)$ such that

$$u < 1 - 4p(1-p) \quad \text{or} \quad \delta^{\frac{u}{2-u} - \left(\frac{2}{q^*(p, u)} - 1\right)} < 4p(1-p),$$

there is a natural number $k$ with

$$4 \sum_{1 \le \lvert S\rvert \le k} \lvert S\rvert\, (1 - u)^{\lvert S\rvert - 1}\, \hat f(S)^2 \le \left(\delta^{u/(2-u)} - 4p(1-p)(1 - u)^k\right) I.$$

Here $q^*(p, u) = 1 + (1 - u)/(4p(1-p))$ is the [exponent paired with $u$](dtr-qstar.md), $\hat f(S)$ are the [$p$-biased Fourier coefficients](../../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/pbiased-tensorize/ptn-coeff.md) of $f$, and $\delta = \max_e \mathrm{Inf}_e$ and $I = \sum_e \mathrm{Inf}_e$ are the maximal and total [influence](../../osss-inequality-for-decision-trees/infl.md) under the $p$-biased product measure.
