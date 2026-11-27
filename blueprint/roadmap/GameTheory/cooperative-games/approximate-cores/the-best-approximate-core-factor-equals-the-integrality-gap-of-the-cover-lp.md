# The best approximate-core factor equals the integrality gap of the cover LP

For a subadditive cost-sharing game, the minimum of $\sum_S \lambda_S c(S)$ over integral balanced families equals $c(A)$. Hence, when $c(A) > 0$, the largest $\gamma$ for which the $\gamma$-core is nonempty equals the integrality gap $\mathrm{LP} / \mathrm{IP}$ of the cover program $\min \sum_S \lambda_S c(S)$ over balanced weights.

## Proof sketch

An integral balanced family is a partition of $A$, whose cost is at least $c(A)$ by subadditivity, with equality for the trivial partition. Combine with the approximate Bondareva–Shapley theorem.

## Depends on

- [Cost-sharing game and its γ-approximate core](cost-sharing-game-and-its-approximate-core.md)
- [Integrality gaps of linear programming relaxations](../../../ComputerScience/approximation-algorithms/lp-based-approximation/integrality-gaps-of-linear-programming.md)

## Proof depends on

- [Bondareva–Shapley characterization of the γ-core](bondareva-shapley-characterization-of-the-core.md)

## Sources

- Kamal Jain and Mohammad Mahdian, "Cost Sharing", Algorithmic Game Theory, Cambridge University Press, 2007.
