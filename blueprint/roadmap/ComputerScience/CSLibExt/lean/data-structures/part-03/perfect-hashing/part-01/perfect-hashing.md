---
declaration: structure
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.PerfectHashing
---

# Perfect Hashing

A static two-level (FKS) hash table. The primary hash selects a bucket
`primaryHash k % bucketCount`; inside bucket `i`, the secondary hash selects the slot
`secondaryHash i k % secondarySize i` of a table with one binding per slot. No
existence or expected-time claim about the hash functions is made; correctness is
conditioned on `PerfectHashing.Valid`.

## Depends on

This node has no prerequisites.

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.PerfectHashing](../../../../../../../../sources/v2/CSLibExt.md)
