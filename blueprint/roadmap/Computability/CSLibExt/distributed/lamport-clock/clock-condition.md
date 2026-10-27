---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Distributed.LamportClock.clock_condition
---

# The clock condition

**The clock condition** (Lamport 1978): if `a` happened before `b`, the
timestamp of `a` is smaller than the timestamp of `b`.

## Depends on

- [Event](event.md)
- [Happens Before](happens-before.md)
- [Timestamps](timestamps.md)

## Proof depends on

- [Step](step.md)
- [Step lt](step-lt.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Distributed.LamportClock](../../../../../sources/v2/CSLibExt.md)
