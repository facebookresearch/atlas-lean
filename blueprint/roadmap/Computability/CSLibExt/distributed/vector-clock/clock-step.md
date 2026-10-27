---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Distributed.VectorClock.clockStep
---

# Clock Step

The vector clock algorithm on one event; timestamps are accumulated in an
array, for constant-time append and lookup.

## Depends on

- [Event](../lamport-clock/event.md)

## Proof depends on

- [Stamp](stamp.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Distributed.VectorClock](../../../../../sources/v2/CSLibExt.md)
