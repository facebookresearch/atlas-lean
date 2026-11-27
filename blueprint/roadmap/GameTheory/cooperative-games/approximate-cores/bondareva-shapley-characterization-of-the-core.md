# Bondareva–Shapley characterization of the γ-core

For every cost-sharing game $c$ and every real $\gamma$, the $\gamma$-core is nonempty if and only if $\gamma\, c(A) \le \sum_S \lambda_S\, c(S)$ for every balanced family of weights $\lambda$. Equivalently, the largest $\gamma$ with nonempty $\gamma$-core is the ratio of the optimum of the fractional cover LP $\min \sum_S \lambda_S c(S)$ over balanced $\lambda$ to $c(A)$ (when $c(A) > 0$).

## Proof sketch

The maximum of $\sum_j \alpha_j$ subject to $\sum_{j \in S}\alpha_j \le c(S)$ equals by strong LP duality the minimum of $\sum_S \lambda_S c(S)$ over balanced $\lambda$; the $\gamma$-core is nonempty iff this maximum is at least $\gamma c(A)$.

## Depends on

- [Cost-sharing game and its γ-approximate core](cost-sharing-game-and-its-approximate-core.md)

## Proof depends on

- [Bondareva–Shapley theorem](../bondareva-shapley-theorem/bondareva-shapley.md)

## Sources

- Kamal Jain and Mohammad Mahdian, "Cost Sharing", Algorithmic Game Theory, Cambridge University Press, 2007.
