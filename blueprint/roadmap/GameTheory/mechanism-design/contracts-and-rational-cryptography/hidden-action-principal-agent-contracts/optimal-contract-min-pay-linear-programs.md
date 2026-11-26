# Optimal contracts via one linear program per action

In a principal-agent instance, for each action $i$ let $\mathrm{MP}_i$ be the optimum of the linear program

$$
\min_{t \in \mathbb{R}_{\ge 0}^m} \; T_i(t) \quad \text{s.t.} \quad T_i(t) - c_i \ge T_k(t) - c_k \;\; \text{for all actions } k,
$$

with $\mathrm{MP}_i = +\infty$ if it is infeasible. The optimal principal utility equals $\max_i (R_i - \mathrm{MP}_i)$, attained by an optimal solution of the program for a maximizing $i$. Hence an optimal contract can be computed in time polynomial in $n$ and $m$.

## Proof sketch

Any contract induces some best-response action $i$ and satisfies that action's incentive constraints, so its payment is at least $\mathrm{MP}_i$. Conversely, an optimal solution of the $i$-th program makes $i$ a best response; tie-breaking in favour of the principal ensures the principal obtains at least $R_i - \mathrm{MP}_i$. Each program has $m$ variables and $n$ constraints.

## Depends on

- [Hidden-action principal-agent instance and contract](hidden-action-principal-agent-instance.md)

## Sources

- S. J. Grossman, O. D. Hart, "An Analysis of the Principal-Agent Problem", Econometrica 51(1) (1983).
- P. Dütting, T. Roughgarden, I. Talgam-Cohen, "Simple versus Optimal Contracts", EC 2019, arXiv:1808.03713.
