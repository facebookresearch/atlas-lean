# Thiele methods for approval committee elections

An approval election consists of a finite set $N$ of $n$ voters, a finite set $C$ of candidates, approval ballots $A_i \subseteq C$ for $i \in N$, and a committee size $k$ with $1 \le k \le \lvert C \rvert$; a committee is a set $W \subseteq C$ with $\lvert W \rvert = k$. A weight sequence is a sequence $w = (w_1, w_2, \dots)$ of nonnegative reals normalized by $w_1 = 1$; the $w_j$ are the increments of the nondecreasing score $j \mapsto \sum_{t \le j} w_t$, so increasing increments such as $w = (1, 2, \dots)$ are allowed. Weight sequences with $w_1 \ge w_2 \ge \cdots$, whose score is concave, are the ones in which further representatives of a voter count less; the examples below are of this kind. The Thiele method with weights $w$ selects committees maximizing $\sum_{i \in N} \sum_{j = 1}^{\lvert A_i \cap W \rvert} w_j$. Approval voting is the case $w_j = 1$ for all $j$, Chamberlin–Courant is $w = (1, 0, 0, \dots)$, and proportional approval voting is $w_j = 1/j$.

## Depends on

- [Approval-based committee elections](../../computational-social-choice/approval-based-committee-elections.md)

## Sources

- M. Lackner, P. Skowron, "Multi-Winner Voting with Approval Preferences", SpringerBriefs in Intelligent Systems (2023), arXiv:2007.01795.
- H. Aziz, M. Brill, V. Conitzer, E. Elkind, R. Freeman, T. Walsh, "Justified Representation in Approval-Based Committee Voting", Social Choice and Welfare 48(2) (2017), arXiv:1407.8269.
