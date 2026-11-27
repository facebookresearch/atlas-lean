# Submodular cost-sharing game

A cost-sharing game is *submodular* (concave) if $c(S \cup T) + c(S \cap T) \le c(S) + c(T)$ for all coalitions $S, T$. An allocation $\alpha$ on a set $T$ is *core-feasible* if $\sum_{j \in S} \alpha_j \le c(S)$ for all $S \subseteq T$, and a coalition $S$ is *tight* if equality holds.

## Depends on

- [Cost-sharing game and its γ-approximate core](../approximate-cores/cost-sharing-game-and-its-approximate-core.md)
- [Submodular set function](../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Sources

- Kamal Jain and Mohammad Mahdian, "Cost Sharing", Algorithmic Game Theory, Cambridge University Press, 2007.
