# Capped estimate implies KKL with constant 2 on $(1/2, q)$

Let $q$ be a real number. If the [capped estimate on $(1/2, q)$](mxd-martingale-hc-statement.md) holds, then so does the following: for every $p$ with $1/2 < p < q$ and $p < 1$, every finite nonempty set $E$ and every indicator $f = 1_A$ of a set $A \subseteq \{0, 1\}^E$, if

$$\frac{1}{p(1-p)} \sum_{\emptyset \ne S \subseteq E} \lvert S\rvert\, \rho^{2(\lvert S\rvert - 1)}\, \hat f(S)^2 \le \delta^{2/q' - 1}\, I$$

for all $\rho \in [0, 1]$ and $q' \in [1, 2]$ with $\rho^2 = 4(q' - 1)p(1-p)$, then $2\, \mathrm{Var}_p(f) \log(1/\delta) \le I$ (with $\log(1/\delta)$ read as $0$ when $\delta = 0$). Here $\hat f(S)$ are the [$p$-biased Fourier coefficients](../../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/pbiased-tensorize/ptn-coeff.md) and $\delta$, $I$ the maximal and total [influence](../../osss-inequality-for-decision-trees/infl.md) under the $p$-biased product measure. The hypothesis on $\rho$ and $q'$ always holds by [per-coordinate hypercontractivity](../../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/pbiased-tensorize/ptn-capped-hc.md), so the capped estimate on $(1/2, q)$ gives the KKL inequality with constant $2$ at every $p \in (1/2, q)$ with $p < 1$.
