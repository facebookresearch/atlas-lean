---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.PerfectHashing.lookup_eq_some_of_stored
---

# Lookup eq some of stored

Completeness of lookup under `Valid`: a stored binding is found, because placement
puts it in exactly the bucket and slot that lookup probes.

## Depends on

- [Perfect Hashing](perfect-hashing.md)
- [Stored](stored.md)
- [Valid](valid.md)
- [Lookup](lookup.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.PerfectHashing](../../../../../../../../sources/v2/CSLibExt.md)
