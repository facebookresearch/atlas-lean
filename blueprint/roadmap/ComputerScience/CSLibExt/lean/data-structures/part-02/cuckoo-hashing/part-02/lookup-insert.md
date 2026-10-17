---
article_id: af_2e78c84709fa21e48aab8a5f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.CuckooHashing.lookup_insert
---

# Lookup insert

Looking up a successfully inserted key returns the inserted value, for tables satisfying
`Valid` and `KeyDet`. The inserted pair sits in one of the key's two slots in the result
(`stored_insert`), and the two invariants rule out a competing value in the other slot.

## Depends on

- [Cuckoo Hashing](../part-01/cuckoo-hashing.md)
- [Key Det](../part-01/key-det.md)
- [Valid](../part-01/valid.md)
- [Insert](../part-01/insert.md)
- [Lookup](../part-01/lookup.md)

## Proof depends on

- [Stored](../part-01/stored.md)
- [Insert Aux](../part-01/insert-aux.md)
- [Lookup eq some of stored](../part-01/lookup-eq-some-of-stored.md)
- [Lookup eq some of table1](../part-01/lookup-eq-some-of-table1.md)
- [Lookup eq some of table2](../part-01/lookup-eq-some-of-table2.md)
- [Slot Has Key](../part-01/slot-has-key.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.CuckooHashing](../../../../../../../../sources/v2/CSLibExt.md)
