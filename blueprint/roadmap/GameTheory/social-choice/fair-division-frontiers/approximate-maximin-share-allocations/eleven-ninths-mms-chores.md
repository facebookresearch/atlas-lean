# Eleven-ninths maximin share approximation for chores

Let $n$ agents have additive cost functions $c_i(S) = \sum_{e \in S} c_i(e)$ with $c_i(e) \ge 0$ on a finite set $M$ of chores. The maximin share of agent $i$ is $\mu_i = \min_{(P_1, \dots, P_n)} \max_k c_i(P_k)$ over partitions of $M$ into $n$ bundles. There always exists a complete allocation $X$ with $c_i(X_i) \le \tfrac{11}{9}\, \mu_i$ for every agent, and such an allocation can be computed in polynomial time up to an arbitrarily small additive loss in the factor. Conversely, there are instances with three agents in which every allocation gives some agent cost at least $\tfrac{44}{43}\, \mu_i$.

## Proof sketch

After reduction to ordered instances, the algorithm builds bundles one at a time with a first-fit-decreasing procedure: the next bundle is filled with the largest chores that fit within $\tfrac{11}{9}$ of some agent's maximin share, and that agent takes it. The analysis mirrors the classical $\tfrac{11}{9}$ bound for first-fit-decreasing bin packing, comparing with each agent's own maximin partition. The lower bound adapts the matrix constructions used for goods.

## Proof depends on

- [Reduction to ordered instances for maximin share approximation](ordered-instance-reduction-mms.md)

## Sources

- X. Huang, P. Lu, "An Algorithmic Framework for Approximating Maximin Share Allocation of Chores", EC 2021, arXiv:1907.04505.
- U. Feige, A. Sapir, L. Tauber, "A tight negative example for MMS fair allocations", WINE 2021, arXiv:2104.04977.
