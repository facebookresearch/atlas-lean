# Regret decomposition for stochastic bandits

Let $\nu = (P_1, \dots, P_k)$ be a stochastic $k$-armed bandit whose arms have finite means
$\mu_1, \dots, \mu_k$, let $\mu^* = \max_i \mu_i$ and $\Delta_i = \mu^* - \mu_i$. For every policy $\pi$
and horizon $n \in \mathbb{N}$, the regret satisfies

$$R_n(\pi, \nu) = \sum_{i=1}^k \Delta_i\, \mathbb{E}[T_i(n)],$$

where $T_i(n)$ is the number of rounds among the first $n$ in which arm $i$ is chosen.

## Depends on

- [Stochastic k-armed bandits: canonical history law](stochastic-k-armed-bandits-canonical-history-law-and-regret.md)
- [Regret of a bandit policy](canonical-bandit-model/regret.md)
- [Pull count of an arm](canonical-bandit-model/pull-count.md)
- [Bandits with finite means](canonical-bandit-model/has-finite-means.md)

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Lemma 4.5. <https://tor-lattimore.com/downloads/book/book.pdf>
