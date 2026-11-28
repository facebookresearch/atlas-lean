# EFX with high Nash welfare by donating items

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. The Nash welfare of a possibly partial allocation $X$, one that may leave goods unallocated (donated to charity), is the geometric mean $\mathrm{NW}(X) = \bigl(\prod_{i=1}^n v_i(X_i)\bigr)^{1/n}$, and $\mathrm{opt}(M)$ is the maximum Nash welfare over complete allocations of $M$. Given a maximum Nash welfare allocation $X$ of $M$, an algorithm (Algorithm 1 of the source) that only permanently removes goods from the bundles computes in polynomial time a partial allocation $Y$ with $Y_i \subseteq X_i$ for every agent $i$ which is EFX, is Pareto optimal among allocations of the goods it keeps, and satisfies $2^{1 - 1/n} \cdot \mathrm{NW}(Y) \ge \mathrm{opt}(M)$; in particular its Nash welfare is at least half of the maximum. The factor is asymptotically best possible: for every $n$ and $\varepsilon > 0$ there is an instance in which every EFX allocation $Z$ of every subset of the goods satisfies $(2^{1 - 1/n} - 2\varepsilon) \cdot \mathrm{NW}(Z) \le \mathrm{opt}(M)$. Starting instead from a $\rho$-approximate allocation $X$, one with $\rho \cdot \mathrm{NW}(X) \ge \mathrm{opt}(M)$, the first algorithm has no such guarantee; a modified procedure (Algorithm 2) either returns an EFX partial allocation or a new input allocation of substantially higher Nash welfare, and running it again on each new input until it returns an EFX allocation $Y$ takes $O(n^2)$ executions for constant $\rho$, hence polynomial time, and gives $2\rho \cdot \mathrm{NW}(Y) \ge \mathrm{opt}(M)$.

## Proof sketch

Start from a maximum Nash welfare allocation and never move goods between bundles. In each round compute a matching of agents to the current bundles in the graph of EFX-feasible pairs, preferring to match agents to their initial bundles and matching every bundle already touched. If the matching is perfect, return it; otherwise remove one good from the robust demand bundle of an unmatched agent, which keeps the matching from shrinking. The maximality of the Nash welfare of the initial allocation, through the local swap inequality, bounds how much value any bundle can lose for the agent who held it initially, by at most a factor $2$, which yields the Nash welfare guarantee. For a $\rho$-approximate input the swap inequality may fail; Algorithm 2 detects each failure and outputs the improved allocation instead, and since after every $n$ such restarts the Nash welfare grows by a factor $1 + \delta$ with $\delta = 1/(2n+1)$ while it never exceeds $\mathrm{opt}(M)$, the restarts stop and the final EFX allocation keeps the factor $2\rho$.

## Depends on

- [Partial EFX allocation with an unallocated pool](../efx-allocations-charity-and-counterexamples/partial-efx-allocation-with-pool.md)
- [Maximum Nash welfare allocation](../../../not-yet-classified/part-01/max-nash-welfare/is-max-nash-welfare.md)

## Proof depends on

- [Local swap inequality at a maximum Nash welfare allocation](mnw-local-swap-inequality.md)
- [Envy graph and most envious agent of a partial allocation](../efx-allocations-charity-and-counterexamples/envy-graph-most-envious-agent.md)

## Sources

- I. Caragiannis, N. Gravin, X. Huang, "Envy-Freeness Up to Any Item with High Nash Welfare: The Virtue of Donating Items", EC 2019, arXiv:1902.04319.
