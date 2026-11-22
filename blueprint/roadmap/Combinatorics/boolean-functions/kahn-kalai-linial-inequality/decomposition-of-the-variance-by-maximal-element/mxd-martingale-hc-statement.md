# Capped influence estimate for all $p$ in $(1/2, q)$

For a real number $q$, the capped estimate on $(1/2, q)$ is the assertion that for every $p$ with $1/2 < p < q$ and $p < 1$, every finite nonempty set $E$, every indicator $f = 1_A$ of a set $A \subseteq \{0, 1\}^E$ and every $u \in [0, 1]$,

$$\sum_{\emptyset \ne S \subseteq E} 4 \lvert S\rvert\, (1 - u)^{\lvert S\rvert - 1}\, \hat f(S)^2 \le \delta^{u/(2-u)}\, I,$$

where $\hat f(S)$ are the [$p$-biased Fourier coefficients](../../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/pbiased-tensorize/ptn-coeff.md) of $f$, and $\delta = \max_e \mathrm{Inf}_e$ and $I = \sum_e \mathrm{Inf}_e$ are the maximal and total [influence](../../osss-inequality-for-decision-trees/infl.md) under the $p$-biased product measure.
