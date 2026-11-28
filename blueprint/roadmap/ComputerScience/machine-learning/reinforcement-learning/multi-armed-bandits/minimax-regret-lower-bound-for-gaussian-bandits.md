# Minimax regret lower bound for Gaussian bandits

Let $k \ge 2$ and $n \ge k - 1$. For every policy $\pi$ there is a mean vector $\mu \in [0,1]^k$ such that, in the
Gaussian bandit $\nu_\mu$ whose arm $i$ has law $\mathcal{N}(\mu_i, 1)$, the regret satisfies
$R_n(\pi, \nu_\mu) \ge \tfrac{1}{27}\sqrt{(k-1)\,n}$. The proof combines the divergence decomposition on the
canonical bandit model with the Bretagnolle–Huber inequality and the regret decomposition.

## Expansion

This node states a precise result. A good expansion adds a page for the pending prerequisite below and links it under the dependency sections.

- Proof prerequisite: the Bretagnolle–Huber inequality $P(A) + Q(A^c) \ge \tfrac12 \exp(-\mathrm{KL}(P, Q))$.

## Depends on

- [Stochastic k-armed bandits: canonical history law](stochastic-k-armed-bandits-canonical-history-law-and-regret.md)
- [Regret of a bandit policy](canonical-bandit-model/regret.md)

## Proof depends on

- [Divergence decomposition for stochastic bandits](divergence-decomposition-for-stochastic-bandits.md)
- [Regret decomposition for stochastic bandits](regret-decomposition-for-stochastic-bandits.md)

## Related topics

- [Lai-Robbins asymptotic lower bound](lai-robbins-asymptotic-lower-bound.md)

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Theorem 15.2 and its proof (Lemma 15.1, Lemma 4.5 and the Bretagnolle–Huber inequality, Theorem 14.2). <https://tor-lattimore.com/downloads/book/book.pdf>
