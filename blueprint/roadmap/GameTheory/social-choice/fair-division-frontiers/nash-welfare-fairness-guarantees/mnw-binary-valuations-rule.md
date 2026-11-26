# Maximum Nash welfare with binary valuations is efficiently computable, fair and group-strategyproof

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. Assume binary valuations. A maximum Nash welfare allocation (maximizing the number of agents with positive value, then the product of positive values) can be computed in polynomial time. With a lexicographic tie-breaking rule among Nash-welfare maximizers chosen to maximize the leximin of the utility vector, the resulting deterministic allocation rule is EFX (for desired goods), Pareto optimal, and group-strategyproof: no coalition of agents can misreport their desired sets so that all of them weakly gain and some strictly gain. A randomized version that mixes over Nash-welfare-maximizing allocations is ex ante envy-free and ex post EF1.

## Proof sketch

With binary valuations, maximizing Nash welfare is equivalent to finding a utility vector that is leximin-optimal among integral flows in the bipartite agent-good graph, since the Nash product is Schur-concave and the set of achievable utility vectors forms the integer points of a polymatroid; leximin over a polymatroid is computable by successive maximum-flow computations. Group-strategyproofness follows because misreporting can only shrink the polymatroid relevant to the deviators' true utilities, and the leximin-optimal point of a polymatroid is monotone under such restrictions.

## Depends on

- [Binary additive valuations](binary-additive-valuations.md)
- [Maximum Nash welfare allocation](../../../not-yet-classified/part-01/max-nash-welfare/is-max-nash-welfare.md)

## Proof depends on

- [Maximum Nash welfare implies EF1](../../../not-yet-classified/part-01/max-nash-welfare-ef1/is-ef1-of-is-max-nash-welfare.md)
- [Refined maximum Nash welfare allocations are Pareto optimal](../../../not-yet-classified/part-01/max-nash-welfare/is-pareto-optimal-of-is-max-nash-welfare.md)

## Sources

- D. Halpern, A. D. Procaccia, A. Psomas, N. Shah, "Fair Division with Binary Valuations: One Rule to Rule Them All", WINE 2020, arXiv:2007.06073.
- A. Darmann, J. Schauer, "Maximizing Nash product social welfare in allocating indivisible goods", European Journal of Operational Research 247(2) (2015).
