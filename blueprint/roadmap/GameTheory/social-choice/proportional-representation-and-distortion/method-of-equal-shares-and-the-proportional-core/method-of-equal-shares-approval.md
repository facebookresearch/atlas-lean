# Method of Equal Shares for approval committees

An approval election consists of a finite set $N$ of $n$ voters, a finite set $C$ of candidates, approval ballots $A_i \subseteq C$ for $i \in N$, and a committee size $k$ with $1 \le k \le \lvert C \rvert$; a committee is a set $W \subseteq C$ with $\lvert W \rvert = k$. Each voter starts with a budget $b_i = k/n$ and each candidate costs $1$. Starting with $W = \emptyset$, repeat: for each $c \notin W$ with $\sum_{i \in N_c} b_i \ge 1$, let $\rho_c$ be the least $\rho \ge 0$ with $\sum_{i \in N_c} \min(b_i, \rho) = 1$; if no candidate is affordable stop, otherwise add a candidate $c$ minimizing $\rho_c$ and set $b_i := b_i - \min(b_i, \rho_c)$ for $i \in N_c$. The rule outputs the set $W$ reached at that point. It satisfies $\lvert W \rvert \le k$, since each selected candidate uses up one unit of the total budget $k$, and it may have fewer than $k$ members: for instance $W = \emptyset$ when every ballot is empty, as then no candidate is affordable. Peters and Skowron show that this possibly short output is priceable. A committee of size $k$ is obtained, if desired, by a separate completion step, for example filling the remaining seats with sequential Phragmén started from the leftover budgets, and arbitrarily once no further candidate approved by some voter remains.

## Depends on

- [Approval-based committee elections](../../computational-social-choice/approval-based-committee-elections.md)

## Sources

- D. Peters, P. Skowron, "Proportionality and the Limits of Welfarism", EC 2020, arXiv:1911.11747.
- D. Peters, G. Pierczyński, P. Skowron, "Proportional Participatory Budgeting with Additive Utilities", NeurIPS 2021, arXiv:2008.13276.
