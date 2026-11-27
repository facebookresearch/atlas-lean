# Maximum bang-per-buck allocation supported by prices

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. A price vector is $p \in \mathbb{R}_{>0}^{M}$. The maximum bang-per-buck ratio of agent $i$ is $\alpha_i = \max_{g \in M} v_i(g)/p_g$, and $\mathrm{MBB}_i = \{ g : v_i(g) = \alpha_i p_g \}$. A complete (possibly fractional) allocation $x = (x_{ig})$, that is, a fractional allocation with $x_{ig} \ge 0$ and $\sum_i x_{ig} = 1$ for every good, is supported by $p$ if $x_{ig} > 0$ implies $g \in \mathrm{MBB}_i$. The pair $(X, p)$ for an integral allocation $X$ is a Fisher market equilibrium with budgets $e_i$ if it is supported by $p$ and $p(X_i) = e_i$ for every $i$.

## Depends on

- [Fractional Pareto optimality](fractional-pareto-optimality.md)

## Sources

- S. Barman, S. K. Krishnamurthy, R. Vaish, "Finding Fair and Efficient Allocations", EC 2018, arXiv:1707.04731.
