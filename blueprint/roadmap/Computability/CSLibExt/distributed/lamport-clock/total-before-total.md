---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Distributed.LamportClock.totalBefore_total
---

# Lamport's order is total

**Lamport's order is total** on the events of an execution: two events of
the same process have different timestamps (rule IR1), so ties only occur
between different processes, which the process order breaks.

## Depends on

- [Event](event.md)
- [Total Before](total-before.md)

## Proof depends on

- [Timestamp lt of proc](timestamp-lt-of-proc.md)
- [Timestamps](timestamps.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Distributed.LamportClock](../../../../../sources/v2/CSLibExt.md)
