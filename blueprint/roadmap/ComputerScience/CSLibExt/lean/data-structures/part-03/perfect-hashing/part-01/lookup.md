---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.PerfectHashing.lookup
---

# Lookup

Looks up a key by evaluating the primary and secondary hashes and inspecting the
single selected slot. Returns the stored value when that slot holds the key, and
`none` otherwise (in particular when the bucket's secondary table is empty).

## Depends on

- [Perfect Hashing](perfect-hashing.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.PerfectHashing](../../../../../../../../sources/v2/CSLibExt.md)
