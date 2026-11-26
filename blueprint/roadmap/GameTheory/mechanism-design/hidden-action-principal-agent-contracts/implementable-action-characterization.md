# Implementable actions are exactly those not replicated more cheaply by a mixture

In a principal-agent instance, action $i$ is implementable (some contract $t \ge 0$ satisfies $T_i(t) - c_i \ge T_k(t) - c_k$ for all actions $k$) if and only if there is no probability distribution $\lambda$ over the actions $k \ne i$ such that

$$
\sum_{k \ne i} \lambda_k F_k = F_i \qquad \text{and} \qquad \sum_{k \ne i} \lambda_k c_k < c_i .
$$

## Proof sketch

Write the incentive constraints as $(F_i - F_k) \cdot t \ge c_i - c_k$ with $t \ge 0$. By Farkas' lemma the system is infeasible iff there are $y_k \ge 0$ with $\sum_k y_k (F_i - F_k) \le 0$ componentwise and $\sum_k y_k (c_i - c_k) > 0$. Since each $F_i - F_k$ has coordinates summing to zero, the componentwise inequality forces equality, so after normalizing $y$ to a distribution $\lambda$ we get $\sum_k \lambda_k F_k = F_i$ and $\sum_k \lambda_k c_k < c_i$.

## Depends on

- [Hidden-action principal-agent instance and contract](hidden-action-principal-agent-instance.md)

## Sources

- B. E. Hermalin, M. L. Katz, "Moral Hazard and Verifiability: The Effects of Renegotiation in Agency", Econometrica 59(6) (1991).
- P. Dütting, T. Roughgarden, I. Talgam-Cohen, "Simple versus Optimal Contracts", EC 2019, arXiv:1808.03713.
