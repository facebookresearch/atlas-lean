---
article_id: af_6c2f851dd20e95e27c603d4d
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.CuckooHashing.insertAux
---

# Insert Aux

The eviction loop: place `cur` in the first table (if `first`) or the second table at its
hash slot, evicting any occupant to its other table in turn. Returns `none` when the fuel
runs out.

## Depends on

- [Cuckoo Hashing](cuckoo-hashing.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.CuckooHashing](../../../../../../../../sources/v2/CSLibExt.md)
