# Verifying extended or proportional justified representation is coNP-complete

An approval election consists of a finite set $N$ of $n$ voters, a finite set $C$ of candidates, approval ballots $A_i \subseteq C$ for $i \in N$, and a committee size $k$ with $1 \le k \le \lvert C \rvert$; a committee is a set $W \subseteq C$ with $\lvert W \rvert = k$. The problem of deciding, given an election and a committee $W$, whether $W$ provides EJR is coNP-complete; the same holds for PJR. Computing a PAV-optimal committee is NP-hard. Nevertheless a committee providing EJR can be computed in polynomial time, for instance by a local-search variant of PAV that only accepts swaps improving the score by at least $n/k^2$.

## Proof sketch

Membership in coNP: a violating $\ell$-cohesive group is a short certificate. Hardness, for EJR and for PJR, reduces from balanced biclique: cohesive groups of the right size and common approvals correspond to bicliques of the bipartite voter-candidate graph, and the committee is chosen so that only such a group can violate the axiom. For local-search PAV, the threshold $n/k^2$ bounds the number of improving swaps by $O(k^2 \log k)$ and the proof of the PAV theorem shows that the local optimum still satisfies EJR.

## Depends on

- [Extended justified representation](extended-justified-representation.md)
- [Proportional justified representation](proportional-justified-representation.md)
- [Thiele methods for approval committee elections](thiele-methods.md)

## Proof depends on

- [Proportional approval voting satisfies extended justified representation](pav-satisfies-ejr.md)
- [Marginal contributions of a committee under proportional approval voting sum to the number of represented voters](pav-marginal-contribution-identity.md)
- [BALANCED BICLIQUE is NP-complete](../../../../TheoryOfComputation/np-completeness/graph-covering-and-domination/balanced-biclique/balanced-biclique-np-complete.md)

## Sources

- H. Aziz, M. Brill, V. Conitzer, E. Elkind, R. Freeman, T. Walsh, "Justified Representation in Approval-Based Committee Voting", Social Choice and Welfare 48(2) (2017), arXiv:1407.8269.
- H. Aziz, E. Elkind, S. Huang, M. Lackner, L. Sánchez-Fernández, P. Skowron, "On the Complexity of Extended and Proportional Justified Representation", AAAI 2018.
