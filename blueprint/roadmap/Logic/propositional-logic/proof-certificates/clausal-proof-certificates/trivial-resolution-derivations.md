# Trivial resolution derivations

A *trivial resolution* derivation is a linear (input) resolution sequence $C_1, D_1, \dots$ in which a clause $E_0$ is resolved successively with clauses $C_1, C_2, \dots, C_r$, each step resolving on a distinct variable that does not reappear afterwards: $E_i$ is the resolvent of $E_{i-1}$ and $C_i$. Reverse unit propagation of a clause $C$ from a formula, with hints $h_1,\dots,h_k$, corresponds to a trivial resolution derivation of a subclause of $C$ from the hinted clauses, read backwards from the last (conflict) clause.

## Depends on

- [Resolvent of two clauses](../../resolution/resolvent.md)
- [RUP and RAT clauses](../rup-and-rat-clauses.md)

## Sources

- P. Beame, H. Kautz and A. Sabharwal, "Towards Understanding and Harnessing the Potential of Clause Learning", Journal of Artificial Intelligence Research 22, 319–351, 2004.
- L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt Jr., M. Kaufmann and P. Schneider-Kamp, "Efficient Certified RAT Verification", Automated Deduction — CADE 26, LNCS 10395, 2017.
