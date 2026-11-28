# MBB-supported price envy-freeness up to one good implies EF1

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. Assume every agent values some good positively and every good is valued positively by some agent. If $X$ is supported by prices $p > 0$ in the maximum bang-per-buck sense and $(X, p)$ is pEF1, then $X$ is EF1 and fractionally Pareto optimal.

## Proof sketch

For agents $i, j$ choose $g$ as in pEF1. Then $v_i(X_i) = \alpha_i\, p(X_i) \ge \alpha_i\, p(X_j \setminus \{g\}) \ge v_i(X_j \setminus \{g\})$, using that $X_i$ consists of MBB goods and that $v_i(h) \le \alpha_i p_h$ for every good $h$. Fractional Pareto optimality is the first welfare theorem.

## Depends on

- [Price envy-freeness up to one good](price-envy-freeness-up-to-one-good.md)
- [Maximum bang-per-buck allocation supported by prices](maximum-bang-per-buck-allocation.md)
- [Is EF1](../../../not-yet-classified/part-01/indivisible/is-ef1.md)
- [Fractional Pareto optimality](fractional-pareto-optimality.md)

## Proof depends on

- [First welfare theorem: price-supported allocations are fractionally Pareto optimal](first-welfare-theorem-mbb-fpo.md)

## Sources

- S. Barman, S. K. Krishnamurthy, R. Vaish, "Finding Fair and Efficient Allocations", EC 2018, arXiv:1707.04731.
