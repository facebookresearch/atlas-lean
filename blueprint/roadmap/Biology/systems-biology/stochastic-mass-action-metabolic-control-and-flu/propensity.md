# Stochastic mass-action propensity

Let $N$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with finite species set $S$ and finite reaction set $\rho$, and let $k \in \mathbb{R}^\rho$ be rate constants. The stochastic mass-action propensity of
reaction $r$ in a state $x \in \mathbb{N}^S$ (molecule counts) is

$$\lambda_r(x) = k_r \prod_{s \in S} x_s (x_s - 1) \cdots (x_s - \mathrm{src}(r)_s + 1),$$

a product of falling factorials, which vanishes when $x_s < \mathrm{src}(r)_s$ for some $s$ (Anderson,
Craciun & Kurtz, arXiv:0803.3042v4, §3.1, eq. (3.4)).
