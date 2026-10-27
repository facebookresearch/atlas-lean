---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Logic.FOL.Derivable.relabel_of_infinite
---

# Relabel of infinite

Derivations survive relabeling free variables along any map (Mathlib's `Formula.relabel`),
when the target has infinitely many variables: each eigenvariable is sent to a fresh one.

## Depends on

- [Natural deduction](../../natural-deduction/derivable.md)

## Proof depends on

- [Formula relabel eq rename](../../syntax/formula-relabel-eq-rename.md)
- [Instantiate](../../syntax/instantiate.md)
- [Instantiate Term](../../syntax/instantiate-term.md)
- [Rename](../../syntax/rename.md)
- [Rename Term](../../syntax/rename-term.md)
- [Rename congr of eq On](rename-congr-of-eq-on.md)

## Sources

- [CSLibExt, CSLibExt.Logics.FirstOrder.Completeness](../../../../../../sources/v2/CSLibExt.md)
