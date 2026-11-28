# Integral form of the mean-field equation

Let $G$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
species set $S$ and finite reaction set $\rho$, let $\beta_r \colon \mathbb{R}^S \to \mathbb{R}$ be
real functions, one for each reaction $r$, and let $x$ be a
[solution of the mean-field equation](is-solution.md) $x' = \sum_r \beta_r(x)\, \zeta_r$ on
$t \ge 0$. Let $t \ge 0$ and suppose that each function $s \mapsto \beta_r(x(s))$ is continuous on
$[0, t]$. Then for every species $i$,

$$x(t)_i = x(0)_i + \sum_{r \in \rho} \left(\int_0^t \beta_r(x(s))\, ds\right) \zeta_r(i),$$

where $\zeta_r$ is the [reaction vector](reaction-vector.md) of $r$.
