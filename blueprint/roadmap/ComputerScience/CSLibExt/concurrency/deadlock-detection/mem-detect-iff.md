---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Concurrency.DeadlockDetection.State.mem_detect_iff
---

# Correctness of deadlock detection

**Correctness of deadlock detection**: a pending process is reported
exactly when no reduction sequence of pending processes finishes it.

## Depends on

- [State](state.md)
- [Reduces](reduces.md)
- [The detection algorithm](detect.md)

## Proof depends on

- [Finished](finished.md)
- [Finished reduces](finished-reduces.md)
- [Reduce Aux](reduce-aux.md)
- [Reduce Aux disjoint](reduce-aux-disjoint.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Concurrency.DeadlockDetection](../../../../../sources/v2/CSLibExt.md)
