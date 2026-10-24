---
article_id: af_8906db622e90a75084f82255
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.CuckooHashing.keyDet_insert
---

# Key Det insert

A successful insertion or replacement preserves key determinism: replacement leaves no
stale copy of the key with a different value in the other slot.

## Depends on

- [Cuckoo Hashing](../part-01/cuckoo-hashing.md)
- [Key Det](../part-01/key-det.md)
- [Valid](../part-01/valid.md)
- [Insert](../part-01/insert.md)

## Proof depends on

- [Stored](../part-01/stored.md)
- [Insert Aux](../part-01/insert-aux.md)
- [Slot Has Key](../part-01/slot-has-key.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.CuckooHashing](../../../../../../../../sources/v2/CSLibExt.md)
