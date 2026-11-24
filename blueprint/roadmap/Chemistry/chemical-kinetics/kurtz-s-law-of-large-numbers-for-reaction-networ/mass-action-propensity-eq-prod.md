# Product formula for the stochastic mass-action propensity

Let $G$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
finite species set $S$ and reaction set $\rho$, let $\kappa \in \mathbb{R}^\rho$ be any real rate
constants (nonnegative in the model), $N$ a natural number, $r$ a reaction with source complex
$k = \mathrm{src}(r)$ and $z \in \mathbb{N}^S$. The
[stochastic mass-action propensity](mass-action-propensity.md) of $r$ at system size $N$ is

$$\lambda^N_r(z) = N \kappa_r \prod_{s \in S} \frac{z_s (z_s - 1)\cdots(z_s - k_s + 1)}{N^{k_s}},$$

with the falling factorial $z_s^{\underline{k_s}}$ in each numerator; it is $1$ when $k_s = 0$ and
$0$ when $z_s < k_s$. At $N = 0$ both sides are $0$, because of the leading factor $N$; the
quotients there follow the convention $a/0 = 0$.
