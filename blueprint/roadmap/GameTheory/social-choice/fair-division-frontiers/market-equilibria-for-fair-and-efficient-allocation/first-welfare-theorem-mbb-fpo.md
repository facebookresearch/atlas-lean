# First welfare theorem: price-supported allocations are fractionally Pareto optimal

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. Assume every agent values some good positively and every good is valued positively by some agent. If an integral allocation $X$ is supported by a price vector $p > 0$ in the maximum bang-per-buck sense, then $X$ is fractionally Pareto optimal. Conversely, every fPO allocation is supported by some positive price vector.

## Proof sketch

Suppose a fractional $y$ Pareto-dominates $X$. For each agent, $v_i(y_i) \le \alpha_i\, p(y_i)$ by definition of $\alpha_i$, while $v_i(X_i) = \alpha_i\, p(X_i)$ since $X$ uses only MBB goods; domination then forces $p(y_i) \ge p(X_i)$ for all $i$ with one strict inequality, contradicting $\sum_i p(y_i) = p(M) = \sum_i p(X_i)$. The converse follows from LP duality for the weighted welfare maximization problem that $X$ solves.

## Depends on

- [Maximum bang-per-buck allocation supported by prices](maximum-bang-per-buck-allocation.md)
- [Fractional Pareto optimality](fractional-pareto-optimality.md)

## Sources

- S. Barman, S. K. Krishnamurthy, R. Vaish, "Finding Fair and Efficient Allocations", EC 2018, arXiv:1707.04731.
