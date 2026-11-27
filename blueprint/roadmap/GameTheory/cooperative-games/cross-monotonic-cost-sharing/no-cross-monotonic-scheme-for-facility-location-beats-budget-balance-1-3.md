# No cross-monotonic scheme for facility location beats budget balance 1/3

For every $\gamma > 1/3$ there is a metric facility location game that admits no $\gamma$-budget-balanced cross-monotonic cost-sharing scheme. One such game has $k$ disjoint groups $A_1, \dots, A_k$ of $m$ agents each and, for every set $B$ containing exactly one agent of each group, a facility $f_B$ of opening cost $3$ at distance $1$ from the agents of $B$ and distance $3$ from all other agents (the shortest-path metric), where $k$ and $m$ are large enough depending on $\gamma$ (the source takes $m = \omega(k)$ and $k = \omega(1)$). Thus the factor $1/3$ is tight.

## Proof sketch

Pick a random group $A_i$ and one random agent from each other group. The chosen coalition $S$ costs $3m + k$ (open one facility serving all of $S$; compare Jain–Mahdian, Lemma 15.22), while cross-monotonicity and budget balance on smaller coalitions bound the expected total share of $S$ by $m(k+3)/k + k + 2$; this is $1/3 + o(1)$ times the cost of $S$ as $k \to \infty$ with $m/k \to \infty$, so some $S$ violates $\gamma$-budget balance.

## Depends on

- [Cooperative facility location game](../approximate-cores/cooperative-facility-location-game.md)
- [Cross-monotonic γ-budget-balanced cost-sharing scheme](cross-monotonic-budget-balanced-cost-sharing-scheme.md)

## Sources

- Kamal Jain and Mohammad Mahdian, "Cost Sharing", Algorithmic Game Theory, Cambridge University Press, 2007.
