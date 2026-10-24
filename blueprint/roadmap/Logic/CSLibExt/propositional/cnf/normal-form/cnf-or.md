---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Logic.PL.Proposition.cnfOr
---

# Cnf Or

`cnfOr ι pos A S`: a CNF of `A` (or its complement) disjoined with the CNF `S`. A chain
of disjunction-like nodes is consumed from the left, so each step distributes one disjunct
over the CNF built so far, whatever the nesting.

## Depends on

- [CNF](../basic/cnf.md)

## Proof depends on

- [Disj](disj.md)
- [CNFClause](../basic/cnfclause.md)

## Sources

- [CSLibExt, CSLibExt.Logics.Propositional.CNF.NormalForm](../../../../../../sources/v2/CSLibExt.md)
