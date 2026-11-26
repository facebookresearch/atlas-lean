# Stochastic mass-action propensity at system size N

(Kurtz 1972.)

Let $G$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
finite species set $S$ and reaction set $\rho$, let $\kappa \in \mathbb{R}^\rho$ be rate constants
and $N$ a natural number, the system size. For a reaction $r$ with source complex
$k = \mathrm{src}(r)$, the stochastic mass-action propensity of $r$ at system size $N$ in a state
$z \in \mathbb{N}^S$ is the
[falling-factorial mass-action propensity](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/propensity.md)
$\lambda_r(z) = \kappa_r \prod_{s \in S} z_s^{\underline{k_s}}$ scaled by the volume:

$$\lambda^N_r(z) = \frac{N\, \lambda_r(z)}{N^{|k|}}, \qquad |k| = \sum_{s \in S} k_s.$$

It vanishes when $z_s < k_s$ for some species $s$. Equivalently, by the
[product formula](mass-action-propensity-eq-prod.md),
$\lambda^N_r(z) = N \kappa_r \prod_{s \in S} \frac{z_s^{\underline{k_s}}}{N^{k_s}}$. At $N = 1$ it
is $\lambda_r(z)$. At $N = 0$ it is $0$: the numerator vanishes, and the denominator $0^{|k|}$ is
$1$ when $|k| = 0$ and $0$ otherwise, where the convention $a/0 = 0$ applies. In the model the rate
constants are nonnegative, as the [stochastic mass-action network](mass-action.md) requires; the
definition allows any real $\kappa$.
