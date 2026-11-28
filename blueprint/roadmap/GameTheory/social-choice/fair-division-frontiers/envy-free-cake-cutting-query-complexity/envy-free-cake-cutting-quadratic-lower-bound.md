# Envy-free cake cutting requires Omega(n^2) queries

Every protocol in the Robertson–Webb query model that always outputs an envy-free allocation of the cake among $n$ agents makes $\Omega(n^2)$ queries in the worst case. In contrast, proportional allocations can be found with $O(n \log n)$ queries by the Even–Paz protocol, and every proportional protocol needs $\Omega(n \log n)$ queries.

## Proof sketch

For the envy-free bound, an adversary answers every query of an agent in a way that refines a partition of $[0, 1]$ associated with that agent by at most two intervals, giving away no further information about how that agent's value is spread inside the current intervals. An envy-free allocation must certify, for many pairs of agents, that a piece is not worth more than the agent's own piece; the adversary shows that this forces each of $\Omega(n)$ agents to have a partition with $\Omega(n)$ intervals, hence $\Omega(n)$ queries per agent. The proportional lower bound is a separate adversary argument.

## Depends on

- [Cake cutting in the Robertson-Webb query model](../../cake-cutting-in-the-robertson-webb-query-model.md)

## Proof depends on

- [Even-Paz proportional protocol](../../even-paz-proportional-protocol.md)

## Sources

- A. D. Procaccia, "Thou Shalt Covet Thy Neighbor's Cake", IJCAI 2009.
- J. Edmonds, K. Pruhs, "Cake cutting really is not a piece of cake", SODA 2006; ACM Transactions on Algorithms 7(4) (2011).
