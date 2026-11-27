# Unique maximal tight set in submodular games

For a submodular cost-sharing game and a core-feasible allocation $\alpha$ on $T$, the tight subsets of $T$ are closed under union and intersection; in particular there is a unique largest tight subset of $T$.

## Proof sketch

For tight $S_1, S_2$, submodularity and core-feasibility give $\alpha(S_1 \cup S_2) + \alpha(S_1 \cap S_2) = c(S_1) + c(S_2) \ge c(S_1 \cup S_2) + c(S_1 \cap S_2) \ge \alpha(S_1\cup S_2) + \alpha(S_1\cap S_2)$, forcing equality.

## Depends on

- [Submodular cost-sharing game](submodular-cost-sharing-game.md)

## Sources

- Kamal Jain and Mohammad Mahdian, "Cost Sharing", Algorithmic Game Theory, Cambridge University Press, 2007.
