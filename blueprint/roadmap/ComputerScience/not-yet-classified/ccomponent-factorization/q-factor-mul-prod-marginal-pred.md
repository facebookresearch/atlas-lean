# C-component factor as a product of conditional marginals

Let a Bayesian network over a finite nonempty alphabet with latent nodes $L$ have observed law $P$, and let $\sigma$ be any topological order of its latent projection. For a c-component $S$ of the projection and observed values $v$, write $v^{<i}$ for the values of the observed nodes before $i$ in $\sigma$. Then

$$Q[S](v)\prod_{i \in S} P(v^{<i}) = \prod_{i \in S} P(v_i, v^{<i}),$$

where $Q[S](v)$ is the probability of $v_S$ under the intervention setting the other observed nodes to $v$. No semi-Markovian assumption is needed. This is the division-free form of Lemma 1(i) of J. Tian and J. Pearl, "A general identification condition for causal effects", AAAI 2002.
