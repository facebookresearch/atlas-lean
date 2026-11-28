# Maximal lotteries

Given a ranking profile on candidates $C$, let $M \in \mathbb{R}^{C \times C}$ be the skew-symmetric majority margin matrix, $M_{ab} = \lvert \{v : a \succ_v b\} \rvert - \lvert \{v : b \succ_v a\} \rvert$. A maximal lottery is a probability distribution $p \in \Delta(C)$ with $p^\top M e_b \ge 0$ for every candidate $b$, i.e. a maximin strategy of the symmetric zero-sum game with payoff matrix $M$. Maximal lotteries exist by the minimax theorem, are unique for an odd number of voters with strict preferences, and place probability one on the Condorcet winner whenever one exists.

## Proof depends on

- [Von Neumann's minimax theorem over every linearly ordered field](../../../../ComputerScience/algebraic-and-numerical-algorithms/linear-programs-as-symmetric-zero-sum-games/minimax-theorem-over-ordered-fields.md)

## Sources

- P. C. Fishburn, "Probabilistic social choice based on simple voting comparisons", Review of Economic Studies 51(4) (1984).
- M. Charikar, P. Ramakrishnan, K. Wang, H. Wu, "Breaking the Metric Voting Distortion Barrier", SODA 2024, arXiv:2306.17838.
