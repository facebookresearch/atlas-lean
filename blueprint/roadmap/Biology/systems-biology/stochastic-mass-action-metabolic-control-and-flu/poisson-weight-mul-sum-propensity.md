# Global balance of the product-form Poisson weights

Let $N$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with finite species set $S$ and finite reaction set $\rho$, let $k \in \mathbb{R}^\rho$ and $c \in \mathbb{R}^S$ with $c$ [complex balanced](../complex-balancing-and-the-deficiency-zero-theore/is-complex-balanced.md) for $k$, and let
$\pi(x) = \prod_s c_s^{x_s} e^{-c_s}/x_s!$ be the [Poisson weights](poisson-weight.md). Then at every state
$x \in \mathbb{N}^S$ the total outflow equals the total inflow:

$$\pi(x) \sum_{r \in \rho} \lambda_r(x) = \sum_{r \,:\, \mathrm{prod}(r) \le x} \pi(x_r)\, \lambda_r(x_r), \qquad x_r = x - \mathrm{prod}(r) + \mathrm{src}(r),$$

with $\lambda_r$ the [propensities](propensity.md) (Anderson, Craciun & Kurtz 2010, Thm 4.1). This identity holds for all real $k$
and $c$.

Equivalently, the Poisson weights $\pi$ solve the
[stationary chemical master equation](../../../Chemistry/chemical-kinetics/ergodic-theorem-for-complex-balanced-reaction-ne/is-stationary-master-solution.md)
with rate constants $k$ at every state of $\mathbb{N}^S$. For $k \ge 0$ and $c \ge 0$ the weights are
nonnegative and
[sum to $1$](../../../Chemistry/chemical-kinetics/ergodic-theorem-for-complex-balanced-reaction-ne/has-sum-poisson-weight.md),
so $\pi$ is then a probability mass function solving that equation.
