# LRAT certificates translate into VeriPB proofs and clausal VeriPB proofs into LRAT

Read the clauses of a CNF formula $\varphi$ as pseudo-Boolean constraints. Every LRAT certificate accepted for $\varphi$ translates step by step into a VeriPB kernel proof accepted for $\varphi$, mapping each RUP step with hints to a pseudo-Boolean RUP step with the same hints and each deletion to a deletion. Conversely a VeriPB proof all of whose steps are *clausal* (RUP steps deriving clauses and deletions) translates into an accepted LRAT certificate whose size and number of hints are linear in those of the VeriPB proof.

## Proof sketch

Clausal unit propagation coincides with pseudo-Boolean propagation on clauses with unit coefficients; hint lists transfer verbatim, with a renumbering of constraint identifiers.

## Depends on

- [Reverse unit propagation for pseudo-Boolean constraints](pseudo-boolean-reverse-unit-propagation.md)
- [Accepted LRAT proofs refute CNF formulas](../accepted-lrat-proofs-refute-cnf-formulas.md)

## Proof depends on

- [Soundness of the VeriPB kernel proof format](veripb-kernel-soundness.md)
- [Accepted LRAT proofs refute CNF formulas](../accepted-lrat-proofs-refute-cnf-formulas.md)

## Sources

- B. Bogaerts, S. Gocht, C. McCreesh and J. Nordström, "Certified Dominance and Symmetry Breaking for Combinatorial Optimisation", Journal of Artificial Intelligence Research 77, 1539–1589, 2023.
- L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt Jr., M. Kaufmann and P. Schneider-Kamp, "Efficient Certified RAT Verification", Automated Deduction — CADE 26, LNCS 10395, 2017.
