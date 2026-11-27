# Trivial resolution derivations

A resolution derivation $(C_1, C_2, \dots, C_k)$ from a clause set $F$ is *trivial* if all variables resolved upon are distinct and each $C_i$ with $i \ge 3$ is either a clause of $F$ or the resolvent of $C_{i-1}$ with a clause of $F$; equivalently, a clause $E_0$ of $F$ is resolved successively with clauses $D_1, \dots, D_r$ of $F$, giving $E_i$ as the resolvent of $E_{i-1}$ and $D_i$, on pairwise distinct variables. If a clause $C \notin F$ has a trivial derivation from $F$, then setting all literals of $C$ to false leads to a conflict by unit propagation; conversely, reverse unit propagation of $C$ with hints $h_1,\dots,h_k$ yields a trivial derivation of a subclause of $C$ from the hinted clauses, read backwards from the last (conflict) clause.

## Depends on

- [Resolvent of two clauses](../../resolution/resolvent.md)
- [RUP and RAT clauses](../rup-and-rat-clauses.md)

## Sources

- P. Beame, H. Kautz and A. Sabharwal, "Towards Understanding and Harnessing the Potential of Clause Learning", Journal of Artificial Intelligence Research 22, 319–351, 2004: Section 3.5, Definition 8 and Propositions 3–4.
- L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt Jr., M. Kaufmann and P. Schneider-Kamp, "Efficient Certified RAT Verification", Automated Deduction — CADE 26, LNCS 10395, 2017.
