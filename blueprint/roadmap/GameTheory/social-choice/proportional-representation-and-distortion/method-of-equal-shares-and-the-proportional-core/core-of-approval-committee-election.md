# Core of an approval-based committee election

An approval election consists of a finite set $N$ of $n$ voters, a finite set $C$ of candidates, approval ballots $A_i \subseteq C$ for $i \in N$, and a committee size $k$ with $1 \le k \le \lvert C \rvert$; a committee is a set $W \subseteq C$ with $\lvert W \rvert = k$. A committee $W$ is in the core if there is no pair $(N', T)$ with a nonempty $N' \subseteq N$, $T \subseteq C$, $\lvert N' \rvert \ge \lvert T \rvert \cdot n/k$, such that $\lvert A_i \cap T \rvert > \lvert A_i \cap W \rvert$ for every $i \in N'$. Nonemptiness matters: for $N' = T = \emptyset$ the remaining conditions hold vacuously, so the empty pair would block every committee; for nonempty $N'$ the strict inequality forces $T \ne \emptyset$. The core property implies EJR. It is an open question, raised in the cited sources, whether every approval election admits a committee in the core.

## Depends on

- [Extended justified representation](../extended-and-proportional-justified-representation/extended-justified-representation.md)

## Sources

- H. Aziz, M. Brill, V. Conitzer, E. Elkind, R. Freeman, T. Walsh, "Justified Representation in Approval-Based Committee Voting", Social Choice and Welfare 48(2) (2017), arXiv:1407.8269.
- D. Peters, P. Skowron, "Proportionality and the Limits of Welfarism", EC 2020, arXiv:1911.11747.
- B. Fain, K. Munagala, N. Shah, "Fair Allocation of Indivisible Public Goods", EC 2018, arXiv:1805.03164.
