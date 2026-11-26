# Pál–Tardos 1/3-budget-balanced cross-monotonic scheme for metric facility location

For every metric facility location game there is a cross-monotonic cost-sharing scheme that is $\tfrac13$-budget-balanced: all agents grow ghost shares uniformly, a facility becomes tight at the time $t$ with $\sum_j \max(0, t - d(i, j)) = f_i$, and an agent's ghost share freezes once it reaches a tight facility, that is, at time $\min_i \max(t_i, d(i, j))$, where the opening time $t_i$ of facility $i$ is $\min_{\emptyset \ne S} (f_i + \sum_{j \in S} d(i, j))/|S|$ over subsets $S$ of the coalition. Moulin's mechanism with this scheme is therefore group-strategyproof and recovers at least a third of the cost.

## Proof sketch

Ghost shares depend on the coalition only through opening times, which decrease as the coalition grows, giving cross-monotonicity. A primal-dual analysis with the metric triangle inequality shows the shares pay for a solution of cost at most three times their sum and never exceed the optimum.

## Depends on

- [Cooperative facility location game](../approximate-cores/cooperative-facility-location-game.md)
- [Cross-monotonic γ-budget-balanced cost-sharing scheme](cross-monotonic-budget-balanced-cost-sharing-scheme.md)

## Proof depends on

- [Moulin's mechanism is group-strategyproof and budget-balanced](moulins-mechanism-is-group-strategyproof-and-budget-balanced.md)

## Sources

- Kamal Jain and Mohammad Mahdian, "Cost Sharing", Algorithmic Game Theory, Cambridge University Press, 2007.
