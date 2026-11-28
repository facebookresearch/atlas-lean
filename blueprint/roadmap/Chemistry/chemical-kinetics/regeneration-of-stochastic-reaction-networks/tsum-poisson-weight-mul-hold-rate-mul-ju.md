# Complex balance makes the Poisson weights balance the jump kernel

Let $N$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with finite sets $S$ of species and
$\rho$ of reactions, $\kappa \in \mathbb{R}^\rho$ with $\kappa_r \ge 0$ for every $r$, and
$c \in \mathbb{R}^S$ with $c_s \ge 0$ for every $s$ that is
[complex balanced](../../../Biology/systems-biology/complex-balancing-and-the-deficiency-zero-theore/is-complex-balanced.md) for $\kappa$. For the
[stochastic mass-action network](mass-action.md) of $N$ and $\kappa$, with
[holding rate](../non-explosion-of-stochastic-reaction-networks/hold-rate.md) $q$ and [jump kernel](../non-explosion-of-stochastic-reaction-networks/jump-pmf.md) $K$,
the [product-form Poisson weights](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/poisson-weight.md)
$\pi_c(x) = \prod_{s \in S} c_s^{x_s} e^{-c_s} / x_s!$ (with $0^0 = 1$) balance
the rate-weighted jump kernel: for every $y \in \mathbb{N}^S$

$$\sum_{x \in \mathbb{N}^S} \pi_c(x)\, q(x)\, K(x, y) = \pi_c(y)\, q(y),$$

a sum of nonnegative terms in $[0, \infty]$, finite by the identity. This is the stationary
master equation of the
[Anderson–Craciun–Kurtz theorem](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/poisson-weight-mul-sum-propensity.md)
written for the jump–hold chain, in which an absorbing state (total propensity $0$) has the
fictitious rate $1$ and jumps to itself.
