---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Concurrency.DeadlockDetection.State.Reduces
---

# Reduces

`Reduces S work σ`: starting with `work` free, each process of `σ` in turn
gets its request, finishes, and releases its allocation.

## Depends on

- [State](state.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Concurrency.DeadlockDetection](../../../../../sources/v2/CSLibExt.md)
