---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Logic.FOL.Derivable.sound
---

# Soundness

**Soundness.** If `Γ ⊢ φ`, then `φ` holds under every assignment satisfying `Γ`, in every
structure.

## Depends on

- [Natural deduction](derivable.md)

## Proof depends on

- [Instantiate](../syntax/instantiate.md)
- [Realize all formula](../syntax/realize-all-formula.md)
- [Realize congr](../syntax/realize-congr.md)
- [Realize instantiate formula](../syntax/realize-instantiate-formula.md)

## Sources

- [CSLibExt, CSLibExt.Logics.FirstOrder.NaturalDeduction](../../../../../sources/v2/CSLibExt.md)
