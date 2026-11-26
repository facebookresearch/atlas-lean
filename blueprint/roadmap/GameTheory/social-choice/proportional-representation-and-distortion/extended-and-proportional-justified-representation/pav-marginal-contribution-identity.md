# Marginal contributions of a committee under proportional approval voting sum to the number of represented voters

An approval election consists of a finite set $N$ of $n$ voters, a finite set $C$ of candidates, approval ballots $A_i \subseteq C$ for $i \in N$, and a committee size $k$ with $1 \le k \le \lvert C \rvert$; a committee is a set $W \subseteq C$ with $\lvert W \rvert = k$. The PAV score is $\mathrm{PAV}(W) = \sum_{i \in N} H(\lvert A_i \cap W \rvert)$ with $H(t) = \sum_{s = 1}^{t} 1/s$. For every committee $W$,

$$
\sum_{w \in W} \bigl(\mathrm{PAV}(W) - \mathrm{PAV}(W \setminus \{w\})\bigr) = \bigl\lvert \{ i \in N : A_i \cap W \ne \emptyset \} \bigr\rvert \le n,
$$

and for every candidate $c \notin W$, $\mathrm{PAV}(W \cup \{c\}) - \mathrm{PAV}(W) = \sum_{i \,:\, c \in A_i} \frac{1}{\lvert A_i \cap W \rvert + 1}$.

## Proof sketch

Removing $w$ lowers voter $i$'s term by $1/\lvert A_i \cap W\rvert$ exactly when $w \in A_i$. Summing over $w \in W$, voter $i$ contributes $\lvert A_i \cap W\rvert \cdot 1/\lvert A_i \cap W\rvert = 1$ if $A_i \cap W \ne \emptyset$ and $0$ otherwise. The formula for adding $c$ is the same computation for one candidate.

## Depends on

- [Approval-based committee elections](../../computational-social-choice/approval-based-committee-elections.md)

## Sources

- H. Aziz, M. Brill, V. Conitzer, E. Elkind, R. Freeman, T. Walsh, "Justified Representation in Approval-Based Committee Voting", Social Choice and Welfare 48(2) (2017), arXiv:1407.8269.
- M. Lackner, P. Skowron, "Multi-Winner Voting with Approval Preferences", SpringerBriefs in Intelligent Systems (2023), arXiv:2007.01795.
