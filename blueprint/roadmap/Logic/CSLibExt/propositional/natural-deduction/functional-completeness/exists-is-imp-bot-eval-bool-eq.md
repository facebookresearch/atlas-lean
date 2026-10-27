---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Logic.PL.exists_isImpBot_evalBool_eq
---

# Functional completeness of `→` and `⊥`

**Functional completeness of `→` and `⊥`**: every Boolean function of the atoms in a
finite list is the truth table, on valuations with `⊥` false, of a proposition built with
`→` alone.

## Depends on

- [Is Imp Bot](is-imp-bot.md)
- [Eval Bool](../semantics/eval-bool.md)

## Proof depends on

- [Eval Bool shannon](eval-bool-shannon.md)
- [Eval Bool to Imp Bot](eval-bool-to-imp-bot.md)
- [Shannon](shannon.md)
- [To Imp Bot](to-imp-bot.md)

## Sources

- [CSLibExt, CSLibExt.Logics.Propositional.NaturalDeduction.FunctionalCompleteness](../../../../../../sources/v2/CSLibExt.md)
