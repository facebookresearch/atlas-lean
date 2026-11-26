# Method of Equal Shares for approval committees

An approval election consists of a finite set $N$ of $n$ voters, a finite set $C$ of candidates, approval ballots $A_i \subseteq C$ for $i \in N$, and a committee size $k$ with $1 \le k \le \lvert C \rvert$; a committee is a set $W \subseteq C$ with $\lvert W \rvert = k$. Each voter starts with a budget $b_i = k/n$ and each candidate costs $1$. Starting with $W = \emptyset$, repeat: for each $c \notin W$ with $\sum_{i \in N_c} b_i \ge 1$, let $\rho_c$ be the least $\rho \ge 0$ with $\sum_{i \in N_c} \min(b_i, \rho) = 1$; if no candidate is affordable stop, otherwise add a candidate $c$ minimizing $\rho_c$ and set $b_i := b_i - \min(b_i, \rho_c)$ for $i \in N_c$. The resulting committee may have fewer than $k$ members; a completion step (for example raising the initial budgets uniformly, or filling with seq-Phragmén) is then applied to reach $k$ members.

## Depends on

- [Approval-based committee elections](../../computational-social-choice/approval-based-committee-elections.md)

## Sources

- D. Peters, P. Skowron, "Proportionality and the Limits of Welfarism", EC 2020, arXiv:1911.11747.
- D. Peters, G. Pierczyński, P. Skowron, "Proportional Participatory Budgeting with Additive Utilities", NeurIPS 2021, arXiv:2008.13276.
