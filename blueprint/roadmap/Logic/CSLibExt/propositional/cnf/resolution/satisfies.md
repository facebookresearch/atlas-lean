---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Logic.PL.CNF.ResolutionDerivable.satisfies
---

# Soundness

**Soundness**: every clause derived by resolution holds under every assignment
satisfying the formula.

## Depends on

- [CNF](../basic/cnf.md)
- [Resolution Derivable](resolution-derivable.md)
- [Satisfies](../semantics/satisfies-3.md)
- [CNFClause](../basic/cnfclause.md)
- [Satisfies](../semantics/satisfies-2.md)

## Proof depends on

- [Resolvent](resolvent.md)
- [Resolution rule soundness](satisfies-resolvent.md)

## Sources

- [CSLibExt, CSLibExt.Logics.Propositional.CNF.Resolution](../../../../../../sources/v2/CSLibExt.md)
