---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Logic.PL.CNF.resolutionDerivable_nil_of_not_cnfSat
---

# Refutation completeness

**Refutation completeness** of resolution: every unsatisfiable CNF formula has a
resolution derivation of the empty clause.

## Depends on

- [CNF](../basic/cnf.md)
- [Resolution Derivable](resolution-derivable.md)
- [CNFSat](../basic/cnfsat.md)

## Proof depends on

- [Lifting lemma](lift-restrict.md)
- [Card vars restrict lt](../restriction/card-vars-restrict-lt.md)
- [Nil mem of vars eq empty](nil-mem-of-vars-eq-empty.md)
- [Restrict](../restriction/restrict-2.md)
- [Sat iff restrict true or false](../restriction/sat-iff-restrict-true-or-false.md)
- [Vars](../restriction/vars-2.md)
- [CNFClause](../basic/cnfclause.md)
- [Resolvent](resolvent.md)

## Sources

- [CSLibExt, CSLibExt.Logics.Propositional.CNF.Resolution](../../../../../../sources/v2/CSLibExt.md)
