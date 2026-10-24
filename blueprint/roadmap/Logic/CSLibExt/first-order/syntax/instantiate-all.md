---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Logic.FOL.instantiate_all
---

# Instantiate all

Under a quantifier the outermost bound variable is still index `0` (de Bruijn levels), so
instantiation passes through unchanged.

## Depends on

- [Instantiate](instantiate.md)

## Proof depends on

- [Instantiate Term](instantiate-term.md)

## Sources

- [CSLibExt, CSLibExt.Logics.FirstOrder.Syntax](../../../../../sources/v2/CSLibExt.md)
