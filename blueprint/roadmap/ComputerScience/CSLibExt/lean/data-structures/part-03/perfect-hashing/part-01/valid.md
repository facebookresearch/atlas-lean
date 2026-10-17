---
declaration: structure
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.PerfectHashing.Valid
---

# Valid

The correctness invariant of a two-level table. `placed` says every stored binding
lies in the bucket selected by the primary hash for its key, at the slot selected by
that bucket's secondary hash. `injective` says each secondary hash is injective, as
a slot selector, on the keys stored in its bucket: no two stored keys of one bucket
collide. The second clause follows from the first (`Valid.injective_of_placed`); it
is recorded separately because choosing such injective secondary hashes is the task
of the FKS construction.

## Depends on

- [Perfect Hashing](perfect-hashing.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.PerfectHashing](../../../../../../../../sources/v2/CSLibExt.md)
