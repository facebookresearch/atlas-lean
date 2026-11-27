# EFX with high Nash welfare by donating items

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. There always exists a partial allocation $X$, leaving some goods unallocated (donated to charity), that is EFX and whose Nash welfare is at least half of the maximum Nash welfare over all complete allocations of $M$. Such an allocation can be computed from any maximum Nash welfare allocation by permanently removing goods from its bundles, and each agent's final bundle is a subset of the bundle she receives in that maximum Nash welfare allocation. The factor $\tfrac12$ is asymptotically best possible: for every $n$ and $\varepsilon > 0$ there are instances in which every EFX allocation of every subset of the goods has Nash welfare at most $\mathrm{opt}/(2^{1 - 1/n} - 2\varepsilon)$. Starting instead from a $\rho$-approximate allocation, the same procedure runs in polynomial time and gives an EFX allocation that is a $2\rho$-approximation.

## Proof sketch

Start from a maximum Nash welfare allocation and never move goods between bundles. In each round compute a matching of agents to the current bundles in the graph of EFX-feasible pairs, preferring to match agents to their initial bundles and matching every bundle already touched. If the matching is perfect, return it; otherwise remove one good from the robust demand bundle of an unmatched agent, which keeps the matching from shrinking. The maximality of the Nash welfare of the initial allocation, through the local swap inequality, bounds how much value any bundle can lose for the agent who held it initially, by at most a factor $2$, which yields the Nash welfare guarantee.

## Depends on

- [Partial EFX allocation with an unallocated pool](../efx-allocations-charity-and-counterexamples/partial-efx-allocation-with-pool.md)
- [Maximum Nash welfare allocation](../../../not-yet-classified/part-01/max-nash-welfare/is-max-nash-welfare.md)

## Proof depends on

- [Local swap inequality at a maximum Nash welfare allocation](mnw-local-swap-inequality.md)
- [Envy graph and most envious agent of a partial allocation](../efx-allocations-charity-and-counterexamples/envy-graph-most-envious-agent.md)

## Sources

- I. Caragiannis, N. Gravin, X. Huang, "Envy-Freeness Up to Any Item with High Nash Welfare: The Virtue of Donating Items", EC 2019, arXiv:1902.04319.
