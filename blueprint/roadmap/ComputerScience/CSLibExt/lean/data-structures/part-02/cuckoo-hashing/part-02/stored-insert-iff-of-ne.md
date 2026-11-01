---
article_id: af_3047ebd305ce8efcaeda7a1f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.CuckooHashing.stored_insert_iff_of_ne
---

# Stored insert iff of ne

A successful insertion or replacement preserves exactly the bindings of
every other key: for `other ≠ key`, a binding is stored after the operation
if and only if it was stored before. The forward direction covers both
replacement paths and the eviction loop; the backward direction rules out
new unrelated bindings.

## Depends on

- [Cuckoo Hashing](../part-01/cuckoo-hashing.md)
- [Stored](../part-01/stored.md)
- [Valid](../part-01/valid.md)
- [Insert](../part-01/insert.md)

## Proof depends on

- [Insert Aux](../part-01/insert-aux.md)
- [Slot Has Key](../part-01/slot-has-key.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.CuckooHashing](../../../../../../../../sources/v2/CSLibExt.md)
