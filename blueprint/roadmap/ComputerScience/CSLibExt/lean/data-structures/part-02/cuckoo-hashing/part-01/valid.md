---
article_id: af_37f5a1493f8a0c9ba50a00b0
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.CuckooHashing.Valid
---

# Valid

The placement invariant: an entry in the first table sits at `h1` of its key, and an entry
in the second table sits at `h2` of its key. This is what lets `lookup` check only two
slots.

## Depends on

- [Cuckoo Hashing](cuckoo-hashing.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.CuckooHashing](../../../../../../../../sources/v2/CSLibExt.md)
