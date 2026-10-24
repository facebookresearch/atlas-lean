---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Distributed.VectorClock.vectorClock_le_of_step
---

# Vector Clock le of step

One step of happened-before does not decrease any entry.

## Depends on

- [Event](../lamport-clock/event.md)
- [Step](../lamport-clock/step.md)
- [Timestamps](timestamps.md)

## Proof depends on

- [Clock Step](clock-step.md)
- [Run](run.md)
- [Run get D](run-get-d.md)
- [Stamp](stamp.md)
- [Timestamp le vector](timestamp-le-vector.md)
- [Timestamps get D eq stamp](timestamps-get-d-eq-stamp.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Distributed.VectorClock](../../../../../sources/v2/CSLibExt.md)
