---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Distributed.VectorClock.eq_or_happensBefore_of_le
---

# The converse direction

**The converse direction**: if the entry of `a`'s process in `a`'s
timestamp is at most that entry in `b`'s timestamp, then `a = b` or `a`
happened before `b`.

## Depends on

- [Event](../lamport-clock/event.md)
- [Happens Before](../lamport-clock/happens-before.md)
- [Timestamps](timestamps.md)

## Proof depends on

- [Step](../lamport-clock/step.md)
- [Clock Step](clock-step.md)
- [One le own](one-le-own.md)
- [Run](run.md)
- [Run get D](run-get-d.md)
- [Stamp](stamp.md)
- [Timestamp le vector](timestamp-le-vector.md)
- [Timestamps get D eq stamp](timestamps-get-d-eq-stamp.md)
- [Vector eq](vector-eq.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Distributed.VectorClock](../../../../../sources/v2/CSLibExt.md)
