---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.PerfectHashing.lookup_empty
---

# Lookup empty

Looking up any key in the empty table returns `none`.

## Depends on

- [Empty](empty.md)
- [Lookup](lookup.md)

## Proof depends on

- [Stored](stored.md)
- [Lookup eq none iff](lookup-eq-none-iff.md)
- [Not stored empty](not-stored-empty.md)
- [Valid empty](valid-empty.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.PerfectHashing](../../../../../../../../sources/v2/CSLibExt.md)
