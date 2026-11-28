# Polynomial communication is required for approximate Nash equilibria

Consider two players, each knowing only her own $N \times N$ payoff matrix with entries in $[0, 1]$. There is a constant $\varepsilon > 0$ such that every randomized communication protocol that outputs an $\varepsilon$-approximate Nash equilibrium of the bimatrix game must communicate $N^{\Omega(1)}$ bits; for $n$-player binary-action games, the communication complexity of an $\varepsilon$-approximate Nash equilibrium (even of an $(\varepsilon, \varepsilon)$-weak one, in which a $1 - \varepsilon$ fraction of the players $\varepsilon$-best-respond) is $2^{\Omega(n)}$. Consequently uncoupled dynamics need $N^{\Omega(1)}$, respectively $2^{\Omega(n)}$, rounds to reach one. In contrast, an $\varepsilon$-approximate correlated equilibrium of a two-player $N$-action game admits a randomized protocol with $(\log N)^{O(1/\varepsilon)}$ bits, which is $\mathrm{polylog}(N)$ for constant $\varepsilon$.

## Proof sketch

Start from a query lower bound for an End-of-Line-type search problem and lift it to randomized communication with a simulation theorem, so that the line structure is split between the two players; a game-embedding of a Brouwer function with an error-correcting code converts approximate equilibria into ends of lines. The correlated equilibrium upper bound follows from fast swap-regret dynamics run jointly by the players.

## Depends on

- [Mixed Nash equilibrium](../is-mixed-nash.md)
- [Nash equilibrium of a bimatrix game](../../bimatrix-games-and-the-lemke-howson-algorithm/is-bimatrix-nash.md)
- [Correlated equilibrium](../../correlated-equilibria/is-correlated-eq.md)
- [Randomized communication complexity](../../../../TheoryOfComputation/communication-complexity/randomized-communication-protocols/rand-complexity.md)

## Proof depends on

- [Swap regret polylogarithmic in the number of actions](../../../../ComputerScience/machine-learning/online-learning-and-boosting/fast-swap-regret-and-correlated-equilibria/polylog-rounds-swap-regret.md)

## Sources

- Y. Babichenko, A. Rubinstein, "Communication complexity of approximate Nash equilibria", STOC 2017; Games and Economic Behavior 134 (2022), arXiv:1608.06580, Corollary 1.1.
- B. Peng, A. Rubinstein, "Fast Swap Regret Minimization and Applications to Approximate Correlated Equilibria", STOC 2024, arXiv:2310.19647, Corollary 1.5.
