# Inflow along one reaction comes from its unique predecessor

Let $N$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
a finite set $S$ of species, $r$ a reaction, $\kappa$ and $c$ arbitrary real vectors of rate
constants and means, and $y \in \mathbb{N}^S$. Let $\pi_c$ be the
[product-form Poisson weight](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/poisson-weight.md),
$\lambda_r$ the
[mass-action propensity](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/propensity.md),
$\mathrm{fire}_r(x) = x - \mathrm{src}(r) + \mathrm{prod}(r)$ the
[state after one firing](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/fire.md)
and $\mathrm{unfire}_r(y) = y - \mathrm{prod}(r) + \mathrm{src}(r)$ the
[state before it](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/unfire.md)
(subtraction truncated at $0$), and write $u^+ = \max(u, 0)$. Then, summing in $[0, \infty]$,

$$\sum_{x \in \mathbb{N}^S \,:\, \mathrm{fire}_r(x) = y} \bigl(\pi_c(x)\, \lambda_r(x)\bigr)^+
= \bigl(\pi_c(w)\, \lambda_r(w)\bigr)^+, \qquad w = \mathrm{unfire}_r(y),$$

when $\mathrm{prod}(r) \le y$, and the sum is $0$ otherwise. Every other state that fires to $y$
lacks the reactants of $r$, so its propensity is $0$. For $c \ge 0$ and $\kappa \ge 0$ the
products are nonnegative and the positive parts can be dropped.
