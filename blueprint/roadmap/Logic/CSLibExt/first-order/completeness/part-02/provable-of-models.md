---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Logic.FOL.provable_of_models
---

# Completeness

**Completeness.** If a formula over `ℕ` holds in every model of a Mathlib theory `T` (in the
universe `max u v`), it is provable from the sentences of `T`.

## Depends on

- [Provable](../../natural-deduction/provable.md)

## Proof depends on

- [Strong completeness](provable-of-entails.md)

## Sources

- [CSLibExt, CSLibExt.Logics.FirstOrder.Completeness](../../../../../../sources/v2/CSLibExt.md)
