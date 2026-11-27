# Fractional Pareto optimality

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. A fractional allocation is a matrix $x = (x_{ig})_{i \in N, g \in M}$ with $x_{ig} \ge 0$ and $\sum_i x_{ig} \le 1$ for every good $g$, so part of a good may stay unallocated (the fractional allocation is complete when $\sum_i x_{ig} = 1$ for every good); it gives agent $i$ value $\sum_g v_i(g) x_{ig}$. An integral allocation $X$ is fractionally Pareto optimal (fPO) if there is no fractional allocation $y$ with $\sum_g v_i(g) y_{ig} \ge v_i(X_i)$ for all $i$ and strict inequality for some $i$. Every fPO allocation is Pareto optimal among integral allocations.

## Depends on

- [Pareto-optimal allocation](../../../not-yet-classified/part-01/indivisible/is-pareto-optimal.md)

## Sources

- S. Barman, S. K. Krishnamurthy, R. Vaish, "Finding Fair and Efficient Allocations", EC 2018, arXiv:1707.04731.
