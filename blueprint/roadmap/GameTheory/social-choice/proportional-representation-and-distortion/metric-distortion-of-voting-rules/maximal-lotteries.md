# Maximal lotteries

Given a ranking profile on candidates $C$, let $M \in \mathbb{R}^{C \times C}$ be the skew-symmetric majority margin matrix, $M_{ab} = \lvert \{v : a \succ_v b\} \rvert - \lvert \{v : b \succ_v a\} \rvert$. A maximal lottery is a probability distribution $p \in \Delta(C)$ with $p^\top M e_b \ge 0$ for every candidate $b$, i.e. a maximin strategy of the symmetric zero-sum game with payoff matrix $M$. Maximal lotteries exist by the minimax theorem, are unique for an odd number of voters with strict preferences, and place probability one on the Condorcet winner whenever one exists.

## Depends on

- [Von Neumann's minimax theorem](../../../noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)
- [Condorcet profile](../../../not-yet-classified/part-01/condorcet-cycle/condorcet-profile.md)

## Sources

- P. C. Fishburn, "Probabilistic social choice based on simple voting comparisons", Review of Economic Studies 51(4) (1984).
- M. Charikar, P. Ramakrishnan, K. Wang, H. Wu, "Breaking the Metric Voting Distortion Barrier", SODA 2024, arXiv:2306.17838.
