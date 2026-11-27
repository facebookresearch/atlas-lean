# Divergence decomposition for stochastic bandits

Fix $k \ge 1$ arms, a horizon $n$, two environments $\nu = (P_1, \dots, P_k)$ and
$\nu' = (P'_1, \dots, P'_k)$ of reward distributions on $\mathbb{R}$, and a policy given by measurable
probability kernels from histories to arms. Let $\mathbb{P}_{\nu}$ and $\mathbb{P}_{\nu'}$ be the laws of
the history $(A_1, X_1, \dots, A_n, X_n)$ on the canonical bandit model. Then

$$\mathrm{KL}(\mathbb{P}_{\nu}, \mathbb{P}_{\nu'}) = \sum_{i=1}^k \mathbb{E}_{\nu}[T_i(n)]\, \mathrm{KL}(P_i, P'_i),$$

where $T_i(n)$ is the number of pulls of arm $i$, relative entropy takes values in $[0, \infty]$, and the
convention $0 \cdot \infty = 0$ applies.

## Expansion

This node states a precise result. A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: relative entropy (Kullback–Leibler divergence) of probability measures on a general measurable space, with values in $[0, \infty]$.
- Proof prerequisite: the chain rule for relative entropy of compositions of probability kernels.

## Depends on

- [Stochastic k-armed bandits: canonical history law and regret](stochastic-k-armed-bandits-canonical-history-law-and-regret.md)

## Related topics

- [Minimax regret lower bound for Gaussian bandits](minimax-regret-lower-bound-for-gaussian-bandits.md)

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Lemma 15.1 (divergence decomposition), on the canonical bandit model of Section 4.6. <https://tor-lattimore.com/downloads/book/book.pdf>
