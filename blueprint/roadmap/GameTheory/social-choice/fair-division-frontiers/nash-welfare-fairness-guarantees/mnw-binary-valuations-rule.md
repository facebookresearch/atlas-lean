# Maximum Nash welfare with binary valuations is efficiently computable, fair and group-strategyproof

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. Assume binary valuations. Then the maximum Nash welfare allocations (maximizing the number of agents with positive value, then the product of positive values) are exactly the leximin allocations. Consider the deterministic rule that, for a fixed order of the agents, returns a maximum Nash welfare allocation whose utility vector is lexicographically greatest in that order (maximize $v_1(X_1)$, then $v_2(X_2)$, and so on), allocating exactly the goods that some agent desires; goods desired by nobody stay unallocated. This rule is EF1, Pareto optimal, group-strategyproof (no coalition of agents can misreport their desired sets so that all of them strictly gain), and computable in polynomial time. Randomizing over maximum Nash welfare allocations yields, in polynomial time, a rule that is ex ante envy-free, ex ante Pareto optimal, ex ante group-strategyproof and ex post EF1.

## Proof sketch

With binary valuations the achievable utility vectors are those of bipartite matchings between agents and desired goods with capacities, so maximum Nash welfare and leximin coincide, and a maximum Nash welfare allocation can be computed with flow-based algorithms; the tie-breaking step then walks to the lexicographically greatest utility vector among them. EF1 and Pareto optimality hold for every maximum Nash welfare allocation. Group-strategyproofness is proved by showing that a deviating coalition cannot raise the true utilities of all its members under the fixed tie-breaking. For the randomized rule, a fractional maximum Nash welfare allocation is ex ante envy-free and Pareto optimal, and it can be decomposed into integral maximum Nash welfare allocations that are each EF1.

## Depends on

- [Binary additive valuations](binary-additive-valuations.md)
- [Maximum Nash welfare allocation](../../../not-yet-classified/part-01/max-nash-welfare/is-max-nash-welfare.md)
- [Pareto-optimal allocation](../../../not-yet-classified/part-01/indivisible/is-pareto-optimal.md)
- [Is EF1](../../../not-yet-classified/part-01/indivisible/is-ef1.md)

## Proof depends on

- [Maximum Nash welfare implies EF1](../../../not-yet-classified/part-01/max-nash-welfare-ef1/is-ef1-of-is-max-nash-welfare.md)
- [Refined maximum Nash welfare allocations are Pareto optimal](../../../not-yet-classified/part-01/max-nash-welfare/is-pareto-optimal-of-is-max-nash-welfare.md)

## Sources

- D. Halpern, A. D. Procaccia, A. Psomas, N. Shah, "Fair Division with Binary Valuations: One Rule to Rule Them All", WINE 2020, arXiv:2007.06073.
- A. Darmann, J. Schauer, "Maximizing Nash product social welfare in allocating indivisible goods", European Journal of Operational Research 247(2) (2015).
