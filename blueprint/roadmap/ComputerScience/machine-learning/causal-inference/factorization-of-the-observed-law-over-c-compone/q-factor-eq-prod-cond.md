# C-component factor as a product of conditionals

Let a Bayesian network over a finite nonempty alphabet have latent nodes $L$, let $\sigma$ be an ordering of the observed nodes compatible with the directed edges of the latent projection, let $S$ be a c-component of the projection, and let $v$ be an observed configuration with $P(v) > 0$. Then $Q[S](v) = \prod_{i \in S} \dfrac{P(v_{\{u : \sigma(u) \le \sigma(i)\}})}{P(v_{\{u : \sigma(u) < \sigma(i)\}})}$, where $P(v_A)$ is the observed marginal on $A$. No semi-Markovian hypothesis is needed.

## Sources

J. Tian and J. Pearl, "A general identification condition for causal effects", AAAI 2002, eq. (29).
