# Hidden-action principal-agent instance and contract

A principal-agent instance consists of $n \ge 1$ actions with costs $0 = c_1 \le c_2 \le \dots \le c_n$, $m$ outcomes with rewards $r_1, \dots, r_m \ge 0$, and for each action $i$ a probability distribution $F_i = (F_{i,1}, \dots, F_{i,m})$ over outcomes. The expected reward of action $i$ is $R_i = \sum_j F_{i,j} r_j$. A contract is a payment vector $t \in \mathbb{R}_{\ge 0}^m$ (limited liability). Under $t$, choosing action $i$ gives the agent expected utility $T_i(t) - c_i$ with $T_i(t) = \sum_j F_{i,j} t_j$, and gives the principal $R_i - T_i(t)$. The agent best-responds with an action maximizing her utility, breaking ties in favour of the principal. Because action $1$ has zero cost and payments are nonnegative, a best response gives the agent utility at least $T_1(t) \ge 0$, so individual rationality (participation) holds automatically and the agent never rejects a contract; without a zero-cost action (for example a single action of cost $1$ under the zero contract) one must instead impose individual rationality $T_i(t) - c_i \ge 0$ and let the agent reject a contract under which no action satisfies it. The principal's utility from $t$ is evaluated at the agent's best response, and an optimal contract maximizes it. The action is hidden: the contract may depend on the realized outcome only.

## Sources

- S. J. Grossman, O. D. Hart, "An Analysis of the Principal-Agent Problem", Econometrica 51(1) (1983).
- P. Dütting, T. Roughgarden, I. Talgam-Cohen, "Simple versus Optimal Contracts", EC 2019, arXiv:1808.03713.
