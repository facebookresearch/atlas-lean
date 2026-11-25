# Stochastic mass-action network with nonnegative rate constants

Let $N$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with a finite set $S$ of species and
reactions indexed by a set $\rho$, and let $\kappa \in \mathbb{R}^\rho$ be rate constants with
$\kappa_r \ge 0$ for every $r$.
The stochastic mass-action network of $N$ and $\kappa$ is the
[stochastic reaction network](../non-explosion-of-stochastic-reaction-networks/stochastic-crn.md) with underlying network $N$ and the
[mass-action propensities](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/propensity.md)

$$\lambda_r(x) = \kappa_r \prod_{s \in S} x_s (x_s - 1) \cdots (x_s - \mathrm{src}(r)_s + 1),
\qquad x \in \mathbb{N}^S.$$

They meet the two conditions of a stochastic reaction network: $\lambda_r(x) \ge 0$, because
$\kappa_r \ge 0$, and $\lambda_r(x) = 0$ when $x$ lacks the reactants of $r$
($x_s < \mathrm{src}(r)_s$ for some $s$), because the falling factorial then has the factor $0$.
Reaction $r$ moves the state $x$ to $x - \mathrm{src}(r) + \mathrm{prod}(r)$, the
[state after one firing](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/fire.md).
