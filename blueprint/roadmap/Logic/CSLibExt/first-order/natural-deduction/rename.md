---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Logic.FOL.Derivable.rename
---

# Rename

Derivations survive an injective renaming of free variables (stated with `FOL.rename`,
which is Mathlib's `Formula.relabel` on formulas by `formula_relabel_eq_rename`; see
`Derivable.relabel`).

## Depends on

- [Natural deduction](derivable.md)
- [Rename](../syntax/rename.md)

## Proof depends on

- [Free Var Finset rename](../syntax/free-var-finset-rename.md)
- [Instantiate](../syntax/instantiate.md)
- [Instantiate Term](../syntax/instantiate-term.md)
- [Rename Term](../syntax/rename-term.md)

## Sources

- [CSLibExt, CSLibExt.Logics.FirstOrder.NaturalDeduction](../../../../../sources/v2/CSLibExt.md)
