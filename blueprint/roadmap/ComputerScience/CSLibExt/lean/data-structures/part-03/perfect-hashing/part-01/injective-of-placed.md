---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.PerfectHashing.Valid.injective_of_placed
---

# Injective of placed

Placement implies secondary injectivity on stored keys: if two stored keys of one
bucket selected the same slot, both bindings would have to occupy that slot, so the
bindings, and in particular the keys, are equal.

## Depends on

- [Perfect Hashing](perfect-hashing.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.PerfectHashing](../../../../../../../../sources/v2/CSLibExt.md)
