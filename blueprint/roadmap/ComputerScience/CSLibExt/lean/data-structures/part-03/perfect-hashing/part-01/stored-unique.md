---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.PerfectHashing.stored_unique
---

# Stored unique

Under `Valid`, the stored value for a key is unique when it exists. This is
a direct consequence of placement (both bindings would occupy the one slot their
shared key hashes to), so it needs no decidable equality on keys.

## Depends on

- [Perfect Hashing](perfect-hashing.md)
- [Stored](stored.md)
- [Valid](valid.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.PerfectHashing](../../../../../../../../sources/v2/CSLibExt.md)
