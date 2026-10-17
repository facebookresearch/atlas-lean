---
article_id: af_3d37060cbc93152e68ffa03b
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.CuckooHashing.insert
---

# Insert

Inserts a binding or replaces the existing binding for the key. An existing binding in
either of the key's slots is overwritten in place; a replacement in the first table also
clears a duplicate copy of the key in its second slot, so no stale competing value
remains. Otherwise the eviction loop runs with the given fuel. Returns `none` when the
loop exhausts its fuel, which models the rehash trigger of the classical algorithm.

## Depends on

- [Cuckoo Hashing](cuckoo-hashing.md)

## Proof depends on

- [Insert Aux](insert-aux.md)
- [Slot Has Key](slot-has-key.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.CuckooHashing](../../../../../../../../sources/v2/CSLibExt.md)
