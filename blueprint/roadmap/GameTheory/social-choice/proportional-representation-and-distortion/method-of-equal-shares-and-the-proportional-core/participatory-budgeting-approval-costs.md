# Participatory budgeting with approval ballots and project costs

A participatory budgeting instance consists of a finite set $N$ of $n$ voters, a finite set $P$ of projects with costs $\mathrm{cost} : P \to \mathbb{R}_{>0}$, a budget $L > 0$ and approval ballots $A_i \subseteq P$. A feasible outcome is $W \subseteq P$ with $\mathrm{cost}(W) = \sum_{p \in W} \mathrm{cost}(p) \le L$. A group $N'$ is $T$-cohesive for $T \subseteq P$ if $T \subseteq \bigcap_{i \in N'} A_i$ and $\lvert N'\rvert / n \ge \mathrm{cost}(T)/L$. An outcome $W$ satisfies EJR (for approval utilities $u_i(W) = \lvert A_i \cap W\rvert$) if for every $T$ and every $T$-cohesive $N'$ there is $i \in N'$ with $\lvert A_i \cap W \rvert \ge \lvert T \rvert$. For general additive utilities $u_i$, a group $N'$ is $(\alpha, T)$-cohesive for $\alpha : P \to [0, 1]$ if $\lvert N'\rvert / n \ge \mathrm{cost}(T)/L$ and $u_i(p) \ge \alpha(p)$ for all $i \in N'$ and $p \in T$; EJR requires some $i \in N'$ with $u_i(W) \ge \sum_{p \in T} \alpha(p)$, and EJR up to one project requires some $i \in N'$ with $u_i(W) \ge \sum_{p \in T} \alpha(p)$ or $u_i(W \cup \{p^*\}) > \sum_{p \in T} \alpha(p)$ for some $p^* \in T$. For approval utilities the two notions coincide. With unit costs and $L = k$ this specializes to approval committee elections.

## Depends on

- [Approval-based committee elections](../../computational-social-choice/approval-based-committee-elections.md)

## Sources

- D. Peters, G. Pierczyński, P. Skowron, "Proportional Participatory Budgeting with Additive Utilities", NeurIPS 2021, arXiv:2008.13276.
