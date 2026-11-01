---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Concurrency.Banker.System.SafeSeq
---

# Safe Seq

`SafeSeq S work σ`: starting with `work` free, each process of `σ` in turn
can be given its remaining need, finish, and release its allocation.

## Depends on

- [System](system.md)

## Proof depends on

- [Need](need.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Concurrency.Banker](../../../../../sources/v2/CSLibExt.md)
