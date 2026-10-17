---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Logic.FOL.Provable.models
---

# Soundness for theories

**Soundness for theories.** A formula provable from the sentences of a Mathlib theory `T`
(embedded as formulas over `α` by `Formula.relabel Empty.elim`) holds in every model of `T`
under every assignment.

## Depends on

- [Provable](provable.md)

## Proof depends on

- [Natural deduction](derivable.md)
- [Soundness](sound.md)

## Sources

- [CSLibExt, CSLibExt.Logics.FirstOrder.NaturalDeduction](../../../../../sources/v2/CSLibExt.md)
