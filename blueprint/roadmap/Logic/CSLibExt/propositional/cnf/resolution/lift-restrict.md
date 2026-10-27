---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Logic.PL.CNF.ResolutionDerivable.lift_restrict
---

# Lifting lemma

**Lifting lemma**: a clause derived from `φ` restricted by `(x, b)` lifts to a clause
derived from `φ` whose literals are among the original ones and `(x, !b)`.

## Depends on

- [CNF](../basic/cnf.md)
- [Resolution Derivable](resolution-derivable.md)
- [Restrict](../restriction/restrict-2.md)
- [CNFClause](../basic/cnfclause.md)

## Proof depends on

- [Mem restrict iff](mem-restrict-iff.md)
- [Resolvent](resolvent.md)
- [Restrict](../restriction/restrict.md)

## Sources

- [CSLibExt, CSLibExt.Logics.Propositional.CNF.Resolution](../../../../../../sources/v2/CSLibExt.md)
