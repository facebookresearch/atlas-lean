# Stochastic mass-action reaction network at system size N

Let $G$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
finite species set $S$ and reaction set $\rho$, let $\kappa \in \mathbb{R}^\rho$ be nonnegative rate
constants, $\kappa_r \ge 0$ for every reaction $r$, and let $N$ be a natural number. The stochastic
mass-action network at system size $N$ is the
[stochastic reaction network](../non-explosion-of-stochastic-reaction-networks/stochastic-crn.md) on
$G$ whose propensities are the [stochastic mass-action propensities](mass-action-propensity.md): for
a reaction $r$ with source complex $k = \mathrm{src}(r)$ and a state $z \in \mathbb{N}^S$,

$$\lambda^N_r(z) = N \kappa_r \prod_{s \in S} \frac{z_s^{\underline{k_s}}}{N^{k_s}}.$$

The nonnegativity of $\kappa$ makes them nonnegative, and the falling factorials make
$\lambda^N_r(z) = 0$ when $z_s < k_s$ for some species $s$, as a stochastic reaction network
requires. For $N = 0$ every propensity is $0$.
