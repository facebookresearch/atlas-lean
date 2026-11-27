# Proportional up to any chore allocations always exist

Let $n$ agents have additive costs $c_i(e) \ge 0$ on a finite set of chores $M$. A complete allocation $X$ is PROPX if for every agent $i$ and every chore $e \in X_i$, $c_i(X_i \setminus \{e\}) \le c_i(M)/n$. For every such instance a PROPX allocation exists and can be computed in polynomial time; the same holds for weighted proportionality with arbitrary entitlements. In contrast, for goods with additive values $v_i$ the corresponding notion, $v_i(X_i \cup \{g\}) \ge v_i(M)/n$ for every agent $i$ and every good $g \notin X_i$, can fail to be satisfiable.

## Proof sketch

First treat identical-ordering instances, in which all agents rank the chores in the same order of cost. Allocate the chores from the most to the least costly, each to a sink of the envy graph, resolving top-trading envy cycles when there is no sink. Because the chore just assigned is the smallest in its holder's bundle, the result is EFX for chores, and EFX implies PROPX. A general reduction converts any algorithm for identical-ordering instances into one for arbitrary instances while preserving PROPX. A separate bid-and-take algorithm handles the weighted case.

## Depends on

- [Fair division of mixed goods and chores](mixed-goods-and-chores-model.md)

## Proof depends on

- [Top-trading envy-cycle elimination gives EF1 for monotone chores](top-trading-envy-cycle-ef1-chores.md)

## Sources

- B. Li, Y. Li, X. Wu, "Almost (Weighted) Proportional Allocations for Indivisible Chores", The Web Conference (WWW) 2022, arXiv:2103.11849.
- H. Aziz, H. Moulin, F. Sandomirskiy, "A polynomial-time algorithm for computing a Pareto optimal and almost proportional allocation", Operations Research Letters 48(5) (2020), arXiv:1909.00740.
