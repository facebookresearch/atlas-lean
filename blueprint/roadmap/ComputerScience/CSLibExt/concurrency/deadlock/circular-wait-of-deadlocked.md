---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Concurrency.Deadlock.AllocState.circularWait_of_deadlocked
---

# Circular Wait of deadlocked

With finitely many processes, a deadlocked set contains a wait-for cycle:
following wait-for edges inside the set must revisit a process.

## Depends on

- [Alloc State](alloc-state.md)
- [Circular Wait](circular-wait.md)
- [Deadlocked](deadlocked.md)

## Proof depends on

- [Waits For](waits-for.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Concurrency.Deadlock](../../../../../sources/v2/CSLibExt.md)
