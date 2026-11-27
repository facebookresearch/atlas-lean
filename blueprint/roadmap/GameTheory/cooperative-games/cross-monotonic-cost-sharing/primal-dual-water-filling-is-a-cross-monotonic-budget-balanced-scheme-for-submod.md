# Primal-dual water filling is a cross-monotonic budget-balanced scheme for submodular games

For every nonnegative submodular cost-sharing game, the water-filling scheme, which for coalition $T$ raises all active agents' shares uniformly from $0$ and freezes the agents of each newly tight set until all agents are frozen, is nonnegative, $1$-budget-balanced and cross-monotonic. Consequently Moulin's mechanism with this scheme is group-strategyproof and budget-balanced for every nonnegative submodular cost function.

## Proof sketch

Freezing whole maximal tight sets keeps the allocation core-feasible and ends with $T$ tight, giving budget balance. Enlarging $T$ adds constraints, so each agent freezes no later, which is cross-monotonicity.

## Depends on

- [Submodular cost-sharing game](submodular-cost-sharing-game.md)
- [Cross-monotonic γ-budget-balanced cost-sharing scheme](cross-monotonic-budget-balanced-cost-sharing-scheme.md)

## Proof depends on

- [Unique maximal tight set in submodular games](unique-maximal-tight-set-in-submodular-games.md)
- [Moulin's mechanism is group-strategyproof and budget-balanced](moulins-mechanism-is-group-strategyproof-and-budget-balanced.md)

## Sources

- Kamal Jain and Mohammad Mahdian, "Cost Sharing", Algorithmic Game Theory, Cambridge University Press, 2007.
