---
article_id: af_8ead401a1291bd7366532219
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.CuckooHashing.lookup_insert_of_ne
---

# Lookup insert of ne

A successful insertion or replacement does not change the lookup result for
any other key, the cuckoo analogue of `HashTable.lookup_insert_of_ne`.

## Depends on

- [Cuckoo Hashing](../part-01/cuckoo-hashing.md)
- [Key Det](../part-01/key-det.md)
- [Valid](../part-01/valid.md)
- [Insert](../part-01/insert.md)
- [Lookup](../part-01/lookup.md)

## Proof depends on

- [Stored](../part-01/stored.md)
- [Key Det insert](key-det-insert.md)
- [Lookup eq some of stored](../part-01/lookup-eq-some-of-stored.md)
- [Lookup sound](../part-01/lookup-sound.md)
- [Stored insert iff of ne](stored-insert-iff-of-ne.md)
- [Valid insert](../part-01/valid-insert.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.CuckooHashing](../../../../../../../../sources/v2/CSLibExt.md)
