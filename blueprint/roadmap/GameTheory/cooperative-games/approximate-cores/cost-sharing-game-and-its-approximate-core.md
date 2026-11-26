# Cost-sharing game and its γ-approximate core

A *cost-sharing game* on a finite agent set $A$ assigns a real cost $c(S)$ to every coalition $S \subseteq A$, with $c(\emptyset) = 0$. For $\gamma \in \mathbb{R}$, a vector $\alpha \in \mathbb{R}^A$ lies in the *$\gamma$-core* if $\sum_{j \in A} \alpha_j \ge \gamma\, c(A)$ (approximate budget balance) and $\sum_{j \in S} \alpha_j \le c(S)$ for every coalition $S$ (no coalition is overcharged). The $1$-core is the core. A family $(\lambda_S)_{S \ne \emptyset}$ of nonnegative weights is *balanced* if $\sum_{S \ni j} \lambda_S = 1$ for every agent $j$, and *integral balanced* if moreover $\lambda_S \in \{0, 1\}$.

## Depends on

- [Cooperative game with transferable utility](../shapley-value/coop-game.md)
- [Core allocation](../bondareva-shapley-theorem/is-core-allocation.md)
- [Balanced cooperative game](../bondareva-shapley-theorem/is-balanced.md)

## Sources

- Kamal Jain and Mohammad Mahdian, "Cost Sharing", Algorithmic Game Theory, Cambridge University Press, 2007.
