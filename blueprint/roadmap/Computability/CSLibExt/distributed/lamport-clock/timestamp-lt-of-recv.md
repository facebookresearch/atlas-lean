---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Distributed.LamportClock.timestamp_lt_of_recv
---

# Timestamp lt of recv

Lamport's rule IR2: on a well-formed execution, a receipt gets a larger
timestamp than the send.

## Depends on

- [Event](event.md)
- [Well Formed](well-formed.md)
- [Timestamps](timestamps.md)

## Proof depends on

- [Step lt](step-lt.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Distributed.LamportClock](../../../../../sources/v2/CSLibExt.md)
