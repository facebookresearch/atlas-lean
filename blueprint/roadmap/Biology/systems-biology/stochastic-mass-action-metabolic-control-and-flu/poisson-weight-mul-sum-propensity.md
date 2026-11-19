# Global balance of the product-form Poisson weights

Let $N$ be a [chemical reaction network](../complex-balancing-and-the-deficiency-zero-theore/reaction-network.md) with finite species set $S$ and finite reaction set $\rho$, let $k \in \mathbb{R}^\rho$ and $c \in \mathbb{R}^S$ with $c$ [complex balanced](../complex-balancing-and-the-deficiency-zero-theore/is-complex-balanced.md) for $k$, and let
$\pi(x) = \prod_s c_s^{x_s} e^{-c_s}/x_s!$ be the [Poisson weights](poisson-weight.md). Then at every state
$x \in \mathbb{N}^S$ the total outflow equals the total inflow:

$$\pi(x) \sum_{r \in \rho} \lambda_r(x) = \sum_{r \,:\, \mathrm{prod}(r) \le x} \pi(x_r)\, \lambda_r(x_r), \qquad x_r = x - \mathrm{prod}(r) + \mathrm{src}(r),$$

with $\lambda_r$ the [propensities](propensity.md) (Anderson, Craciun & Kurtz 2010, Thm 4.1). This identity holds for all real $k$
and $c$.
