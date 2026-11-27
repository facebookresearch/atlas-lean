# Proportional approval voting is the only Thiele method satisfying EJR

An approval election consists of a finite set $N$ of $n$ voters, a finite set $C$ of candidates, approval ballots $A_i \subseteq C$ for $i \in N$, and a committee size $k$ with $1 \le k \le \lvert C \rvert$; a committee is a set $W \subseteq C$ with $\lvert W \rvert = k$. Among all Thiele methods, the one with weights $w_j = 1/j$ (proportional approval voting) is the only one whose every optimal committee provides extended justified representation in all elections; for every other weight sequence $w$ with $w_1 = 1$ the Thiele method with weights $w$ fails EJR, and in fact fails PJR; if $w_j > 1/j$ for some $j$ it even fails justified representation.

## Proof sketch

PAV satisfies EJR by the swap argument. Conversely, suppose $w_j \ne 1/j$ for some $j$. If $w_j > 1/j$, take one group of $k$ voters approving a single candidate $c$ and $k/j$ groups of $j(k-1)$ voters, each approving its own $j$ candidates; the Thiele objective prefers giving every large group all of its $j$ candidates to electing $c$, although the first group is $1$-cohesive, so justified representation fails. If $w_j < 1/j$, a party-list profile in which an $\ell$-cohesive group is under-represented in favour of first representatives of other groups gives an EJR violation, and a similar construction violates PJR.

## Depends on

- [Thiele methods for approval committee elections](thiele-methods.md)
- [Extended justified representation](extended-justified-representation.md)
- [Proportional justified representation](proportional-justified-representation.md)
- [Checking justified representation](../../computational-social-choice/checking-justified-representation.md)

## Proof depends on

- [Proportional approval voting satisfies extended justified representation](pav-satisfies-ejr.md)

## Sources

- H. Aziz, M. Brill, V. Conitzer, E. Elkind, R. Freeman, T. Walsh, "Justified Representation in Approval-Based Committee Voting", Social Choice and Welfare 48(2) (2017), arXiv:1407.8269.
- L. Sánchez-Fernández, E. Elkind, M. Lackner, N. Fernández, J. A. Fisteus, P. Basanta Val, P. Skowron, "Proportional Justified Representation", AAAI 2017, arXiv:1611.09928.
