---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Concurrency.Banker.System.Safe.exists_runnable
---

# Exists runnable

A safe state with pending processes is not deadlocked: some pending process
can be given its whole remaining need.

## Depends on

- [System](system.md)
- [Safe](safe.md)
- [Need](need.md)

## Proof depends on

- [Safe Seq](safe-seq.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Concurrency.Banker](../../../../../sources/v2/CSLibExt.md)
