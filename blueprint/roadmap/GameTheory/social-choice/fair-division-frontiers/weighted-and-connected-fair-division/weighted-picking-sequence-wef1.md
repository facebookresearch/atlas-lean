# A weighted picking sequence yields WEF1 allocations

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. Consider the picking sequence in which, at each step, the agent $i$ minimizing $t_i/w_i$ picks her most valuable remaining good, where $t_i$ is the number of goods she has picked so far (ties broken arbitrarily but consistently). The resulting complete allocation is WEF1, and it can be computed in polynomial time. Moreover, fix any largest set $N_{\max} \subseteq N$ of agents that can simultaneously receive bundles of positive value (several such sets may exist, with different optimal products); an allocation that maximizes $\prod_{i \in N_{\max}} v_i(X_i)^{w_i}$ among the allocations giving every agent of $N_{\max}$ positive value is a maximum weighted Nash welfare allocation, and every such allocation, for every choice of $N_{\max}$, is Pareto optimal but in general not WEF1.

## Proof sketch

Fix agents $i, j$. Up to the moment when $i$ makes her $k$-th pick, $j$ has made at most about $k w_j / w_i$ picks (by the choice rule), and each of $i$'s picks is at least as valuable to $i$ as every good $j$ picks later. Pairing $i$'s picks with $j$'s picks in this proportion, after removing $j$'s first pick, gives $v_i(X_j \setminus \{g\})/w_j \le v_i(X_i)/w_i$. An explicit two-agent instance shows weighted Nash welfare can violate WEF1.

## Depends on

- [Weighted envy-freeness up to one good](weighted-envy-freeness-up-to-one-good.md)
- [Pareto-optimal allocation](../../../not-yet-classified/part-01/indivisible/is-pareto-optimal.md)

## Proof depends on

- [Round-robin allocation is envy-free up to one good](../../../cooperative-games/fair-division-of-indivisible-goods/round-robin-allocation-is-ef1.md)

## Sources

- M. Chakraborty, A. Igarashi, W. Suksompong, Y. Zick, "Weighted Envy-Freeness in Indivisible Item Allocation", ACM Transactions on Economics and Computation 9(3) (2021); AAMAS 2020, arXiv:1909.10502.
