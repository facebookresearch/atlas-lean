# Polynomial communication is required for approximate Nash equilibria

Consider two players, each knowing only her own $N \times N$ payoff matrix with entries in $[0, 1]$. There is a constant $\varepsilon > 0$ such that every randomized communication protocol that outputs an $\varepsilon$-approximate Nash equilibrium of the bimatrix game must communicate $N^{\Omega(1)}$ bits; for $n$-player binary-action games, the communication complexity of an $\varepsilon$-approximate Nash equilibrium is $2^{\Omega(n)}$, and uncoupled dynamics require exponentially many rounds to reach one. In contrast, an $\varepsilon$-approximate correlated equilibrium of a bimatrix game admits a protocol with $\mathrm{polylog}(N)$ bits for constant $\varepsilon$.

## Proof sketch

Reduce from set disjointness through a communication variant of End-of-Line, in which the successor structure is split between the two players; a simulation theorem lifts query lower bounds for finding the end of a line to communication lower bounds, and a game-embedding of a Brouwer function with an error-correcting code converts approximate equilibria into ends of lines. The correlated equilibrium upper bound follows from fast swap-regret dynamics run jointly by the players.

## Depends on

- [Computing a Nash equilibrium of a two-player game is PPAD-complete](two-player-nash-ppad-complete.md)
- [Correlated equilibrium](../../correlated-equilibria/is-correlated-eq.md)

## Proof depends on

- [Swap regret polylogarithmic in the number of actions](../../../../ComputerScience/machine-learning/online-learning-and-boosting/fast-swap-regret-and-correlated-equilibria/polylog-rounds-swap-regret.md)

## Sources

- Y. Babichenko, A. Rubinstein, "Communication complexity of approximate Nash equilibria", STOC 2017; Games and Economic Behavior 134 (2022).
- B. Peng, A. Rubinstein, "Fast Swap Regret Minimization and Applications to Approximate Correlated Equilibria", STOC 2024, arXiv:2310.19647.
