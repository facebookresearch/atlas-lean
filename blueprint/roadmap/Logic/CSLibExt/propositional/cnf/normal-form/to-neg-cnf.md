---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Logic.PL.Proposition.toNegCNF
---

# To Neg CNF

A CNF of the Boolean complement of `A`: it holds exactly when `A` is false
(`satisfies_toNegCNF_iff`). This is not upstream's `¬A = A → ⊥`, which can be true when
`A` is, if the atom `⊥` is true.

## Depends on

- [CNF](../basic/cnf.md)

## Proof depends on

- [Cnf Of](cnf-of.md)

## Sources

- [CSLibExt, CSLibExt.Logics.Propositional.CNF.NormalForm](../../../../../../sources/v2/CSLibExt.md)
