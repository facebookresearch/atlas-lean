---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Distributed.VectorClock.happensBefore_iff_lt
---

# Vector clocks characterize happened-before

**Vector clocks characterize happened-before**: for two events of an
execution, `a` happened before `b` exactly when `a`'s timestamp is smaller than
`b`'s in the pointwise order.

## Depends on

- [Event](../lamport-clock/event.md)
- [Happens Before](../lamport-clock/happens-before.md)
- [Timestamps](timestamps.md)

## Proof depends on

- [Lt](../lamport-clock/lt.md)
- [The converse direction](eq-or-happens-before-of-le.md)
- [Vector Clock le of happens Before](vector-clock-le-of-happens-before.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Distributed.VectorClock](../../../../../sources/v2/CSLibExt.md)
