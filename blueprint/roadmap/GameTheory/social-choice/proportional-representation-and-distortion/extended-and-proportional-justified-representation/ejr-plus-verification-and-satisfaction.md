# EJR+ strengthens EJR, is verifiable in polynomial time, and is satisfied by PAV and equal shares

An approval election consists of a finite set $N$ of $n$ voters, a finite set $C$ of candidates, approval ballots $A_i \subseteq C$ for $i \in N$, and a committee size $k$ with $1 \le k \le \lvert C \rvert$; a committee is a set $W \subseteq C$ with $\lvert W \rvert = k$. Every committee satisfying EJR+ provides EJR, and every committee satisfying PJR+ provides PJR. Whether a committee satisfies EJR+ can be decided in polynomial time, and PJR+ can also be decided in polynomial time. Every PAV-optimal committee and every committee output by the Method of Equal Shares satisfies EJR+, and, when every candidate is approved by at least one voter ($N_c \ne \emptyset$ for all $c \in C$, the standing assumption under which Brill, Freeman, Janson and Lackner define the rule and the division below makes sense), sequential Phragmén (which builds the committee in $k$ rounds from zero voter loads, each round adding a candidate $c$ minimizing $(1 + \sum_{i \in N_c} \ell_i)/\lvert N_c \rvert$ and setting the load $\ell_i$ of every $i \in N_c$ to that value) satisfies PJR+.

## Proof sketch

An EJR violation by an $\ell$-cohesive group yields a commonly approved candidate outside $W$ and the same group witnesses an EJR+ violation. To verify EJR+, for each $c \notin W$ and each $\ell \in \{1, \dots, k\}$ check whether at least $\ell n/k$ voters of $N_c$ have fewer than $\ell$ approved members in $W$. PJR+ verification reduces, for each $c$ and $\ell$, to a coverage-type check solvable via submodular minimization. The satisfaction results follow by re-running the swap argument for PAV and the budget argument for equal shares with the single witness candidate $c$; sequential Phragmén satisfies PJR+ because its outputs are priceable with a total voter budget exceeding $k$ when every candidate costs $1$ (with unit voter budgets: with a price below $n/k$), and every committee priceable in this way satisfies PJR+.

## Depends on

- [EJR+ and PJR+ proportionality axioms](ejr-plus-and-pjr-plus.md)
- [Extended justified representation](extended-justified-representation.md)
- [Proportional justified representation](proportional-justified-representation.md)
- [Thiele methods for approval committee elections](thiele-methods.md)
- [Method of Equal Shares for approval committees](../method-of-equal-shares-and-the-proportional-core/method-of-equal-shares-approval.md)
- [Sequential Phragmén satisfies proportional justified representation](sequential-phragmen-satisfies-pjr.md)

## Proof depends on

- [Proportional approval voting satisfies extended justified representation](pav-satisfies-ejr.md)
- [Marginal contributions of a committee under proportional approval voting sum to the number of represented voters](pav-marginal-contribution-identity.md)
- [Priceable committee in an approval election](../method-of-equal-shares-and-the-proportional-core/priceable-committee.md)

## Sources

- M. Brill, J. Peters, "Robust and Verifiable Proportionality Axioms for Multiwinner Voting", EC 2023, arXiv:2302.01989.
- M. Brill, R. Freeman, S. Janson, M. Lackner, "Phragmén's Voting Methods and Justified Representation", AAAI 2017; Mathematical Programming 203 (2024).
- D. Peters, P. Skowron, "Proportionality and the Limits of Welfarism", EC 2020, arXiv:1911.11747.
