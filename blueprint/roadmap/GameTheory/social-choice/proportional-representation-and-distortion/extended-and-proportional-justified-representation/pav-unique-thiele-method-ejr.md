# Proportional approval voting is the only Thiele method satisfying EJR

An approval election consists of a finite set $N$ of $n$ voters, a finite set $C$ of candidates, approval ballots $A_i \subseteq C$ for $i \in N$, and a committee size $k$ with $1 \le k \le \lvert C \rvert$; a committee is a set $W \subseteq C$ with $\lvert W \rvert = k$. Among all Thiele methods, the one with weights $w_j = 1/j$ (proportional approval voting) is the only one whose every optimal committee provides extended justified representation in all elections; for every other weight sequence there is an election in which some optimal committee violates even proportional justified representation or EJR.

## Proof sketch

PAV satisfies EJR by the swap argument. Conversely, if $w_j \ne 1/j$ for some smallest $j$, construct a party-list profile with two groups whose sizes are chosen so that the Thiele objective trades off the $j$-th representative of one group against a first representative of another at the wrong ratio: if $w_j > 1/j$ a large group is over-represented at the expense of an $\ell$-cohesive smaller group, and if $w_j < 1/j$ the reverse happens, violating EJR in either case.

## Depends on

- [Thiele methods for approval committee elections](thiele-methods.md)
- [Extended justified representation](extended-justified-representation.md)

## Proof depends on

- [Proportional approval voting satisfies extended justified representation](pav-satisfies-ejr.md)

## Sources

- H. Aziz, M. Brill, V. Conitzer, E. Elkind, R. Freeman, T. Walsh, "Justified Representation in Approval-Based Committee Voting", Social Choice and Welfare 48(2) (2017), arXiv:1407.8269.
