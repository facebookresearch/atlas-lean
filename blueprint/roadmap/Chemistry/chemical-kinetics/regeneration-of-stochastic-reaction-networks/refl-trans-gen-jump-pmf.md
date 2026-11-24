# Reactions of positive propensity give jumps of positive probability

Let $N$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with finite sets $S$ of species and
$\rho$ of reactions, $\kappa \in \mathbb{R}^\rho$ with $\kappa_r \ge 0$ for every $r$,
$\lambda_r$ the [mass-action propensities](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/propensity.md), and
$u, v \in \mathbb{N}^S$. Suppose that
$v$ is reachable from $u$ along reactions with positive propensity: there are states
$u = u_0, u_1, \dots, u_m = v$ ($m \ge 0$) and reactions $r_1, \dots, r_m$ with
$\lambda_{r_i}(u_{i-1}) > 0$ and $u_i = u_{i-1} - \mathrm{src}(r_i) + \mathrm{prod}(r_i)$ for every
$i$. Then $v$ is reachable from $u$ through jumps of positive probability of the
[jump kernel](../non-explosion-of-stochastic-reaction-networks/jump-pmf.md) $K$ of the
[stochastic mass-action network](mass-action.md): the same states satisfy
$K(u_{i-1}, u_i) \ge \lambda_{r_i}(u_{i-1}) / \lambda(u_{i-1}) > 0$, where $\lambda$ is the total
propensity. Only this direction is stated.
