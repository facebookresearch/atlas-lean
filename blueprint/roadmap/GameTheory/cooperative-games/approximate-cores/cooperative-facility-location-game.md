# Cooperative facility location game

A *facility location instance* has facilities $i$ with opening costs $f_i \ge 0$, agents $j$, and connection costs $d(i, j) \ge 0$; it is *metric* if the connection costs extend to a metric. The associated cost-sharing game assigns to a coalition $S$ the minimum, over sets $F$ of opened facilities, of $\sum_{i \in F} f_i + \sum_{j \in S} \min_{i \in F} d(i, j)$ (with $c(\emptyset) = 0$). This game is subadditive.

## Depends on

- [Cost-sharing game and its γ-approximate core](cost-sharing-game-and-its-approximate-core.md)
- [Formulation and LP lower bound for uncapacitated facility location](../../../TheoryOfComputation/np-completeness/set-systems-and-location/facility-location/facility-location-formulation-and-lp-bound.md)

## Sources

- Kamal Jain and Mohammad Mahdian, "Cost Sharing", Algorithmic Game Theory, Cambridge University Press, 2007.
