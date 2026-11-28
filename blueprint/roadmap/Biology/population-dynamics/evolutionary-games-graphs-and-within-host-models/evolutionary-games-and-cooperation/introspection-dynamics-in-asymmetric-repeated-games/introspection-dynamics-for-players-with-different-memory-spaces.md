# Introspection dynamics for players with different memory spaces

**Strategy spaces.** In the infinitely repeated donation game with benefit $b$ and cost $c$, a memory-one strategy is a vector $p = (p_{CC}, p_{CD}, p_{DC}, p_{DD}) \in [0, 1]^4$, where $p_{ij}$ is the probability of cooperating after a round in which the focal player played $i$ and the co-player played $j$. Three nested memory spaces are compared (Schmid et al. 2022, eqs. (10)–(12)):

- memory-one strategies $M = [0, 1]^4$;
- reactive strategies $R = \{p \in M : p_{CC} = p_{DC},\ p_{CD} = p_{DD}\}$, which condition only on the co-player's last move;
- unconditional strategies $U = \{p \in M : p_{CC} = p_{CD} = p_{DC} = p_{DD}\}$.

For strategies $p, q$ whose outcome chain (the [Markov matrix](../../../zero-determinant-strategies-in-iterated-games/markov-matrix.md) on the outcomes $CC, CD, DC, DD$) is primitive, the long-run payoff of player $1$ is $\pi_1 = v \cdot (b - c, -c, b, 0)$, where $v$ is the unique stationary distribution (eqs. (13)–(14)), equivalently the [Press–Dyson determinant ratio](../../../zero-determinant-strategies-in-iterated-games/dot-product-eq-div-pd-det.md) (eqs. (15)–(16)).

**Introspection dynamics** (eqs. (5)–(6)). Two players, restricted to memory spaces $S_1, S_2 \in \{M, R, U\}$ (possibly different), start from strategies $p_1 \in S_1$, $p_2 \in S_2$. At each time step one player $i$, chosen uniformly, draws a uniformly random alternative $p_i' \in S_i$ and switches to it with probability

$$\varrho = \frac{1}{1 + e^{-\beta(\pi_i' - \pi_i)}},$$

where $\pi_i$ and $\pi_i'$ are the payoffs of the current and the alternative strategy against the co-player's current strategy and $\beta \ge 0$ is the strength of selection. After $T$ steps the payoff of memory space $S_i$ against $S_j$ is the time average

$$\bar\pi_{S_i S_j} = \frac{1}{T} \sum_{t = 1}^{T} \pi_{ij}(t).$$

The $3 \times 3$ matrix $(\bar\pi_{S_i S_j})$ then serves as the payoff matrix of a replicator equation $\dot x_{S_i} = x_{S_i}(f_{S_i} - \bar f)$ on the simplex of memory-space frequencies, with $f_{S_i} = \sum_j \bar\pi_{S_i S_j} x_{S_j}$ (eqs. (21)–(24)).

## Depends on

- [Markov Matrix](../../../zero-determinant-strategies-in-iterated-games/markov-matrix.md)
- [Press–Dyson determinant lemma](../../../zero-determinant-strategies-in-iterated-games/dot-product-eq-div-pd-det.md)
- [Solution of the replicator equation](../../../replicator-dynamics/is-solution.md)

## Proof depends on

- [Existence of a stationary distribution](../../../../../Probability/markov-chains/convergence-theorem-for-finite-markov-chains/exists-stationary.md)
- [Uniqueness of the stationary distribution of a primitive chain](../../../../../Probability/markov-chains/convergence-theorem-for-finite-markov-chains/stationary-unique.md)

## Remarks

The switching probability is the logistic (Fermi) function of the payoff gain: it equals $1/2$ for every proposal when $\beta = 0$, so learning is pure drift, and as $\beta \to \infty$ it tends to $1$ for strict improvements and to $0$ for strict losses, so learning becomes a random-order best-improvement walk. Because each player compares a counterfactual strategy against the co-player's actual current strategy, no shared strategy pool is needed, which is why this update suits asymmetric games in which the two players cannot even represent each other's strategies. Since $U \subset R \subset M$, a larger memory never restricts a player, yet in the reported tournaments with $\beta = 100$ and $c/b \in \{0.1, \dots, 0.9\}$ the reactive player obtains a higher time-averaged payoff than its memory-one opponent, $\bar\pi_{R,M} > \bar\pi_{M,R}$ (Table 1): a smaller space concentrates exploration on the strategies that matter against a learner, while self-play still favours larger memory ($\bar\pi_{M,M} > \bar\pi_{R,R} > \bar\pi_{U,U}$, Table 3).

## Sources

- L. Schmid, C. Hilbe, K. Chatterjee and M. A. Nowak, "Direct reciprocity between individuals that use different strategy spaces", PLoS Computational Biology 18 (2022), e1010149, Results (eqs. (5)–(6), Tables 1–3) and Methods (eqs. (9)–(24)), <https://doi.org/10.1371/journal.pcbi.1010149>, PMCID PMC9197081.
