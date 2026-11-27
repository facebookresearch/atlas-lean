# LRAT certificates translate into VeriPB proofs and clausal VeriPB proofs into LRAT

Read the clauses of a CNF formula $\varphi$ as pseudo-Boolean constraints. Every LRAT certificate without RAT steps accepted for $\varphi$ translates step by step into a VeriPB kernel proof accepted for $\varphi$, mapping each RUP step to a pseudo-Boolean RUP step deriving the same clause and omitting the deletions: unit propagation that reaches a conflict on the hinted clauses also reaches one on the whole constraint database. Conversely a VeriPB proof all of whose steps are *clausal* (RUP steps deriving clauses and deletions) translates step by step into an accepted LRAT certificate, each RUP step taking as hints the clauses that propagate in its unit-propagation run, in order, followed by the falsified clause; so each step has at most as many hints as there are clauses in the database at that step.

## Proof sketch

Clausal unit propagation coincides with pseudo-Boolean propagation on clauses with unit coefficients, and propagation on a larger set of clauses derives every literal or conflict that propagation on a subset derives; constraint identifiers are renumbered.

## Depends on

- [Reverse unit propagation for pseudo-Boolean constraints](pseudo-boolean-reverse-unit-propagation.md)
- [Accepted LRAT proofs refute CNF formulas](../accepted-lrat-proofs-refute-cnf-formulas.md)
- [Soundness of the VeriPB kernel proof format](veripb-kernel-soundness.md)

## Sources

- B. Bogaerts, S. Gocht, C. McCreesh and J. Nordström, "Certified Dominance and Symmetry Breaking for Combinatorial Optimisation", Journal of Artificial Intelligence Research 77, 1539–1589, 2023.
- L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt Jr., M. Kaufmann and P. Schneider-Kamp, "Efficient Certified RAT Verification", Automated Deduction — CADE 26, LNCS 10395, 2017.
