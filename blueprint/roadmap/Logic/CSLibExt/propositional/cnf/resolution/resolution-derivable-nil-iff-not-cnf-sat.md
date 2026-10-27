---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Logic.PL.CNF.resolutionDerivable_nil_iff_not_cnfSat
---

# Soundness and refutation completeness

**Soundness and refutation completeness**: a CNF formula has a resolution refutation
iff it is unsatisfiable.

## Depends on

- [CNF](../basic/cnf.md)
- [Resolution Derivable](resolution-derivable.md)
- [CNFSat](../basic/cnfsat.md)

## Proof depends on

- [Not cnf Sat of resolution Derivable nil](not-cnf-sat-of-resolution-derivable-nil.md)
- [Refutation completeness](resolution-derivable-nil-of-not-cnf-sat.md)

## Sources

- [CSLibExt, CSLibExt.Logics.Propositional.CNF.Resolution](../../../../../../sources/v2/CSLibExt.md)
