---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Logic.PL.Proposition.cnfOf
---

# Cnf Of

A CNF of `A` (if `pos`) or of its Boolean complement (if not), with atom `a` as variable
`ι a`. Each call builds only the polarity it is asked for: a CNF-shaped input gets a linear
`cnfOf ι true`, even though its complement is exponential.

## Depends on

- [CNF](../basic/cnf.md)

## Proof depends on

- [CNFClause](../basic/cnfclause.md)
- [Cnf Acc](cnf-acc.md)

## Sources

- [CSLibExt, CSLibExt.Logics.Propositional.CNF.NormalForm](../../../../../../sources/v2/CSLibExt.md)
