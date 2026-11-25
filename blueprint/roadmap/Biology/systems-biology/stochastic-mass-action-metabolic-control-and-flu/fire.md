# State after one reaction firing

Let $N$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with species set $S$ and reaction set $\rho$ (any sets). For a reaction $r$ and a state $x \in \mathbb{N}^S$ (molecule counts), the state after
one firing of $r$ is $x - \mathrm{src}(r) + \mathrm{prod}(r)$, computed coordinatewise with natural-number
subtraction truncated at $0$. It is meaningful when $\mathrm{src}(r) \le x$, the only case in which the
[propensity](propensity.md) can be nonzero.

For a [stochastic chemical reaction network](../../../Chemistry/chemical-kinetics/non-explosion-of-stochastic-reaction-networks/stochastic-crn.md),
the state after $r$ fires is this map for its underlying network: coordinatewise
$\max(x_s - \mathrm{src}(r)_s, 0) + \mathrm{prod}(r)_s$.
