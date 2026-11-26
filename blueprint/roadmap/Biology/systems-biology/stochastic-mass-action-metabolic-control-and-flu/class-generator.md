# Generator of the mass-action chain on a finite state class

Let $N$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with finite species set $S$ and finite reaction set $\rho$, let $k \in \mathbb{R}^\rho$ be rate constants and $\Omega \subseteq \mathbb{N}^S$ a finite
set of states. The generator of the stochastic mass-action chain restricted to $\Omega$ is the matrix
indexed by $\Omega$ with entries

$$Q_{xy} = \sum_{r \in \rho} \lambda_r(x) \bigl([\mathrm{fire}_r(x) = y] - [x = y]\bigr),$$

where $\lambda_r$ are the [propensities](propensity.md), $\mathrm{fire}_r(x)$ is the [state after one firing](fire.md) of $r$, and
$[\cdot]$ is $1$ if the condition holds and $0$ otherwise. It is a
[rate matrix](is-rate-matrix-class-generator.md) when the rate constants are nonnegative and
$\Omega$ is closed under firing.
