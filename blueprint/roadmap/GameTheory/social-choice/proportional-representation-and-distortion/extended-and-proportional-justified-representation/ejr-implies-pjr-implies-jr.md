# Extended justified representation implies proportional, which implies justified representation

An approval election consists of a finite set $N$ of $n$ voters, a finite set $C$ of candidates, approval ballots $A_i \subseteq C$ for $i \in N$, and a committee size $k$ with $1 \le k \le \lvert C \rvert$; a committee is a set $W \subseteq C$ with $\lvert W \rvert = k$. Every committee providing EJR provides PJR, and every committee providing PJR provides justified representation (the case $\ell = 1$). Both implications are strict: there are elections with committees satisfying PJR but not EJR, and committees satisfying justified representation but not PJR.

## Proof sketch

If some $i \in N'$ has $\lvert A_i \cap W\rvert \ge \ell$ then $\lvert W \cap \bigcup_{j \in N'} A_j \rvert \ge \ell$; and PJR at $\ell = 1$ says some member of a $1$-cohesive group approves a committee member. For strictness, take $k = 2$ and two voters who both approve $a$ and $b$, where voter $1$ also approves $c$ and voter $2$ also approves $d$. The two voters form a $2$-cohesive group, and $W = \{c, d\}$ provides PJR (the union of their ballots contains both members) but not EJR (each voter has one approved member). With the ballots $\{a, b\}$ for both voters and a candidate $e$ approved by nobody, $W = \{a, e\}$ provides justified representation but not PJR.

## Depends on

- [Extended justified representation](extended-justified-representation.md)
- [Proportional justified representation](proportional-justified-representation.md)
- [Checking justified representation](../../computational-social-choice/checking-justified-representation.md)

## Sources

- L. Sánchez-Fernández, E. Elkind, M. Lackner, N. Fernández, J. A. Fisteus, P. Basanta Val, P. Skowron, "Proportional Justified Representation", AAAI 2017, arXiv:1611.09928.
- H. Aziz, M. Brill, V. Conitzer, E. Elkind, R. Freeman, T. Walsh, "Justified Representation in Approval-Based Committee Voting", Social Choice and Welfare 48(2) (2017), arXiv:1407.8269.
