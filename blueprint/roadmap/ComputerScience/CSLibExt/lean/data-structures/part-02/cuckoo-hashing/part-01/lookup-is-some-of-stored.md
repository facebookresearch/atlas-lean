---
article_id: af_4337816160060e75c191ab79
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.CuckooHashing.lookup_isSome_of_stored
---

# Lookup is Some of stored

Lookup is complete under `Valid` in the weak sense: a stored key is found. The found value
may differ from the given one if the key is stored with two values; see
`lookup_eq_some_of_stored` for the value-exact form under `KeyDet`.

## Depends on

- [Cuckoo Hashing](cuckoo-hashing.md)
- [Stored](stored.md)
- [Valid](valid.md)
- [Lookup](lookup.md)

## Proof depends on

- [Lookup eq some of table1](lookup-eq-some-of-table1.md)
- [Lookup eq some of table2](lookup-eq-some-of-table2.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.CuckooHashing](../../../../../../../../sources/v2/CSLibExt.md)
