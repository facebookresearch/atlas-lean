# Optimal contracts via one linear program per action

In a principal-agent instance, which has a zero-cost action $1$, for each action $i$ let $\mathrm{MP}_i$ be the optimum of the linear program

$$
\min_{t \in \mathbb{R}_{\ge 0}^m} \; T_i(t) \quad \text{s.t.} \quad T_i(t) - c_i \ge T_k(t) - c_k \;\; \text{for all actions } k,
$$

with $\mathrm{MP}_i = +\infty$ if it is infeasible; a feasible program attains its minimum, since its objective is bounded below by $0$. The program has no individual-rationality constraint $T_i(t) \ge c_i$ because the constraint for $k = 1$ already gives $T_i(t) - c_i \ge T_1(t) \ge 0$; without a zero-cost action one must add $T_i(t) \ge c_i$ to the $i$-th program and compare with the principal's utility $0$ when the agent rejects. The optimal principal utility equals $\max_i (R_i - \mathrm{MP}_i)$, attained by an optimal solution of the program for a maximizing $i$. Hence, for an instance whose rewards, costs and probabilities are rational numbers given in binary, an optimal contract can be computed in time polynomial in $n$, $m$ and the encoding length of the input, by solving the $n$ linear programs.

## Proof sketch

Any contract induces some best-response action $i$ and satisfies that action's incentive constraints, so its payment is at least $\mathrm{MP}_i$. Conversely, an optimal solution of the $i$-th program makes $i$ a best response; tie-breaking in favour of the principal ensures the principal obtains at least $R_i - \mathrm{MP}_i$. Each program has $m$ variables and $n$ constraints.

## Depends on

- [Hidden-action principal-agent instance and contract](hidden-action-principal-agent-instance.md)

## Sources

- S. J. Grossman, O. D. Hart, "An Analysis of the Principal-Agent Problem", Econometrica 51(1) (1983).
- P. Dütting, T. Roughgarden, I. Talgam-Cohen, "Simple versus Optimal Contracts", EC 2019, arXiv:1808.03713.
