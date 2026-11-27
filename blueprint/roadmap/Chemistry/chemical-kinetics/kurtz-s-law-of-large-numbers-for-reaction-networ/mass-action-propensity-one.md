# System size one gives the falling-factorial mass-action propensity

Let $G$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
finite species set $S$ and reaction set $\rho$, and let $\kappa \in \mathbb{R}^\rho$ be any real
rate constants (nonnegative in the model). At system size $N = 1$ the
[stochastic mass-action propensity](mass-action-propensity.md) is the
[falling-factorial mass-action propensity](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/propensity.md):
for every reaction $r$ and every state $z \in \mathbb{N}^S$,

$$\lambda^1_r(z) = \kappa_r \prod_{s \in S} z_s^{\underline{\mathrm{src}(r)_s}}.$$
