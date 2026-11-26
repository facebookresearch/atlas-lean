# Envy-free cake cutting requires Omega(n^2) queries

Every protocol in the Robertson–Webb query model that always outputs an envy-free allocation of the cake among $n$ agents makes $\Omega(n^2)$ queries in the worst case. In contrast, proportional allocations can be found with $O(n \log n)$ queries by the Even–Paz protocol, and every proportional protocol needs $\Omega(n \log n)$ queries.

## Proof sketch

For the envy-free bound, an adversary answers queries so that each agent's valuation is uniform except on small hidden intervals; an envy-free allocation must, for each pair of agents, separate information about the other's hidden structure, forcing $\Omega(n)$ queries per agent on average for $\Omega(n)$ agents. The proportional lower bound is a separate adversary argument building a balanced decision tree over the agents' thresholds.

## Depends on

- [Cake cutting in the Robertson-Webb query model](../../cake-cutting-in-the-robertson-webb-query-model.md)
- [Even-Paz proportional protocol](../../even-paz-proportional-protocol.md)

## Proof depends on

- [Cake cutting in the Robertson-Webb query model](../../cake-cutting-in-the-robertson-webb-query-model.md)

## Sources

- A. D. Procaccia, "Thou Shalt Covet Thy Neighbor's Cake", IJCAI 2009.
- J. Edmonds, K. Pruhs, "Cake cutting really is not a piece of cake", SODA 2006; ACM Transactions on Algorithms 7(4) (2011).
