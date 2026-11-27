# Symmetric zero-sum game and its solutions

A zero-sum matrix game with payoff matrix $P \in K^{N \times N}$ over a linearly ordered field $K$ is *symmetric* if $P$ is skew-symmetric, $P^{\mathsf T} = -P$; its value is $0$. A *solution* of the symmetric game is a mixed strategy $z \in K^N$ with $z \ge 0$, $\sum_k z_k = 1$ and $Pz \ge 0$ componentwise: played against $z$, every pure strategy of the opponent pays at least the value $0$.

## Depends on

- [Von Neumann's minimax theorem](../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)

## Sources

- Ilan Adler, "The equivalence of linear programs and zero-sum games", International Journal of Game Theory 42(1), 165-177, 2013.
