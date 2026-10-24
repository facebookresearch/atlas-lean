---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Logic.FOL.realize_instantiate_formula
---

# Realize instantiate formula

The one-variable case: `instantiate t φ` holds at `v` iff `φ` holds with its bound variable
set to the value of `t`.

## Depends on

- [Instantiate](instantiate.md)

## Proof depends on

- [Instantiate Term](instantiate-term.md)

## Sources

- [CSLibExt, CSLibExt.Logics.FirstOrder.Syntax](../../../../../sources/v2/CSLibExt.md)
