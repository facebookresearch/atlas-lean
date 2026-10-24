---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Concurrency.DeadlockDetection.State.detect_stuck
---

# Every reported process is stuck

**Every reported process is stuck**: it requests more than is free even
after all the processes that the algorithm lets finish have released their
allocations.

## Depends on

- [State](state.md)
- [The detection algorithm](detect.md)
- [Finished](finished.md)

## Proof depends on

- [Reduce Aux](reduce-aux.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Concurrency.DeadlockDetection](../../../../../sources/v2/CSLibExt.md)
