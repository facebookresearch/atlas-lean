# Almost surely every clock of the step sequence is positive

Let $\sigma$ be a measurable space and $K$ a jump kernel on $\sigma$ (a probability mass function
$K(y, \cdot)$ on $\sigma$ for each $y$). Under the
[law of the step sequence](../non-explosion-of-stochastic-reaction-networks/input-measure.md) $\mathbb{P}$ of the jump–hold chain the
steps $\omega_k = (\xi_k, E_k)$, $k \in \mathbb{N}$, are i.i.d. with the
[step law](../non-explosion-of-stochastic-reaction-networks/step-measure.md): $\xi_k : \sigma \to \sigma$ has independent
coordinates $\xi_k(y) \sim K(y, \cdot)$, and the clock $E_k$ is an independent exponential
variable of rate $1$. Then almost surely every clock is positive:

$$\mathbb{P}(E_k > 0 \text{ for every } k \in \mathbb{N}) = 1.$$

Each clock vanishes or is negative with probability $0$, and a countable union of null events is
null. No countability of $\sigma$ is needed.
