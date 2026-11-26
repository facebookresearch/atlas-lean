# Proportional up to any chore allocations always exist

Let $n$ agents have additive costs $c_i(e) \ge 0$ on a finite set of chores $M$. A complete allocation $X$ is PROPX if for every agent $i$ and every chore $e \in X_i$, $c_i(X_i \setminus \{e\}) \le c_i(M)/n$. For every such instance a PROPX allocation exists and can be computed in polynomial time. In contrast, for goods the analogous notion (each agent's value plus any single unallocated-to-her good reaching $v_i(M)/n$) can fail to be satisfiable.

## Proof sketch

Reduce to ordered instances, then allocate chores from the largest to the smallest by a bid-and-take procedure in which an agent accepts a chore as long as her cost stays within her proportional share after removing her smallest assigned chore. Ordering ensures the removed chore is the smallest one assigned, which is exactly what PROPX needs; a counting argument shows all chores are assigned. A three-agent example with one large good and small goods shows PROPX can fail for goods.

## Depends on

- [Fair division of mixed goods and chores](mixed-goods-and-chores-model.md)

## Proof depends on

- [Reduction to ordered instances for maximin share approximation](../approximate-maximin-share-allocations/ordered-instance-reduction-mms.md)

## Sources

- B. Li, Y. Li, X. Wu, "Almost (Weighted) Proportional Allocations for Indivisible Chores", The Web Conference (WWW) 2022, arXiv:2103.11849.
- H. Aziz, H. Moulin, F. Sandomirskiy, "A polynomial-time algorithm for computing a Pareto optimal and almost proportional allocation", Operations Research Letters 48(5) (2020), arXiv:1909.00740.
