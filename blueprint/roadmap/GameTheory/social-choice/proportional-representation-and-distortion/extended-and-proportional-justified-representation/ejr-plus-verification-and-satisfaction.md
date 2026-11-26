# EJR+ strengthens EJR, is verifiable in polynomial time, and is satisfied by PAV and equal shares

An approval election consists of a finite set $N$ of $n$ voters, a finite set $C$ of candidates, approval ballots $A_i \subseteq C$ for $i \in N$, and a committee size $k$ with $1 \le k \le \lvert C \rvert$; a committee is a set $W \subseteq C$ with $\lvert W \rvert = k$. Every committee satisfying EJR+ provides EJR, and every committee satisfying PJR+ provides PJR. Whether a committee satisfies EJR+ can be decided in polynomial time (indeed in time $O(\lvert C \rvert \cdot n \log n)$ after sorting), and PJR+ can also be decided in polynomial time. Every PAV-optimal committee and every committee output by the Method of Equal Shares satisfies EJR+, and sequential Phragmén satisfies PJR+.

## Proof sketch

An EJR violation by an $\ell$-cohesive group yields a commonly approved candidate outside $W$ and the same group witnesses an EJR+ violation. To verify EJR+, for each $c \notin W$ sort $N_c$ by $\lvert A_i \cap W \rvert$ and check for each $\ell$ whether at least $\ell n/k$ of them have fewer than $\ell$ representatives. PJR+ verification reduces, for each $c$ and $\ell$, to a coverage-type check solvable via submodular minimization. The satisfaction results follow by re-running the swap argument for PAV and the budget argument for equal shares with the single witness candidate $c$.

## Depends on

- [EJR+ and PJR+ proportionality axioms](ejr-plus-and-pjr-plus.md)
- [Verifying extended or proportional justified representation is coNP-complete](ejr-pjr-verification-conp-complete.md)

## Proof depends on

- [Proportional approval voting satisfies extended justified representation](pav-satisfies-ejr.md)
- [Marginal contributions of a committee under proportional approval voting sum to the number of represented voters](pav-marginal-contribution-identity.md)

## Sources

- M. Brill, J. Peters, "Robust and Verifiable Proportionality Axioms for Multiwinner Voting", EC 2023, arXiv:2302.01989.
