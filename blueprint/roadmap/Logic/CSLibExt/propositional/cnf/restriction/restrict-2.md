---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Logic.PL.CNF.restrict
---

# Restrict

Simplify a CNF formula using one assigned literal. Clauses containing the
literal are true and disappear; the assigned variable disappears from every
other clause.

## Depends on

- [CNF](../basic/cnf.md)

## Proof depends on

- [CNFClause](../basic/cnfclause.md)
- [Restrict](restrict.md)

## Sources

- [CSLibExt, CSLibExt.Logics.Propositional.CNF.Restriction](../../../../../../sources/v2/CSLibExt.md)
