# The clock condition

In every execution, if the event at position $a$ happened before
the event at position $b$, then the Lamport timestamp of $a$ is smaller than the Lamport
timestamp of $b$ (Lamport 1978).

Lamport states the clock condition for any system of clocks (p. 560) and shows that his implementation rules IR1 and IR2 guarantee it; this theorem is the clock condition for the timestamps those rules compute. The converse fails: concurrent events can receive ordered timestamps.

## Informally uses

- [One step of happened-before raises the timestamp](step-lt.md): each step of a happened-before chain raises the timestamp; the proof inducts on the chain.

## Background

- [Conditions C1 and C2 imply the clock condition](clock-condition-of-c1-c2.md): the same argument for an arbitrary clock, as Lamport presents it.
- [A receipt is stamped later than its send](timestamp-lt-of-recv.md) and [Lamport timestamps increase along each process](timestamp-lt-of-proc.md): conditions C2 and C1 for the timestamps.

## Sources

- L. Lamport, *Time, Clocks, and the Ordering of Events in a Distributed System*, Communications of the ACM 21(7), July 1978, 558–565: "Logical Clocks", Clock Condition, C1, C2, IR1, IR2, p. 560.
