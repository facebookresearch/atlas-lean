---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Logic.PL.Proposition.toImpBot
---

# To Imp Bot

Rewrite `∧` and `∨` with `→` and `⊥`: `A ∧ B` as `(A → (B → ⊥)) → ⊥`, `A ∨ B` as
`(A → ⊥) → B`.

## Depends on

This node has no prerequisites.

## Sources

- [CSLibExt, CSLibExt.Logics.Propositional.NaturalDeduction.FunctionalCompleteness](../../../../../../sources/v2/CSLibExt.md)
