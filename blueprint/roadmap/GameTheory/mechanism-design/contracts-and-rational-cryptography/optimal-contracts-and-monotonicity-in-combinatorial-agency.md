# Optimal contracts and monotonicity in combinatorial agency

In combinatorial agency, the minimal-payment contract inducing a given effort profile makes it a pure Nash equilibrium, in fact a strong equilibrium, and every contract inducing that profile pays each exerting agent at least as much in expectation. For both the first-best and the hidden-action optimum, the success probability is nondecreasing in the principal's value $v$; for anonymous technologies so is the number of exerting agents. For anonymous technologies (depending only on the number of exerting agents), the optimal contract under hidden action can skip intermediate numbers of agents. In the AND and OR technologies in which every agent's task succeeds with probability $\gamma$ without effort and $1 - \gamma$ with effort, the price of unaccountability of anonymous AND technologies is unbounded over $n$ and $\gamma$, while that of every anonymous OR technology with $\gamma \in (0, 1/2)$ is at most $5/2$, for every $n$ and every cost $c$.

## Proof sketch

Agent $i$ exerts effort iff $p_i \Delta_i \ge c_i$, so the minimal contract makes each constraint tight. Monotonicity in $v$ follows from a revealed-preference exchange argument comparing optimal profiles at two values.

## Depends on

- [Combinatorial agency and the price of unaccountability](combinatorial-agency-and-the-price-of-unaccountability.md)
- [Strong equilibrium, strong Nash equilibrium and k-resilience](../../noncooperative-games/potential-games/strong-and-coalitional-equilibria/strong-equilibrium-strong-nash-equilibrium-and-k-resilience.md)

## Sources

- Moshe Babaioff, John Chuang and Michal Feldman, "Incentives in Peer-to-Peer Systems", Algorithmic Game Theory, Cambridge University Press, 2007, Theorems 23.8 and 23.9.
