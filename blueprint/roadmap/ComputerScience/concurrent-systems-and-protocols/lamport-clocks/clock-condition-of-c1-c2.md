# Conditions C1 and C2 imply the clock condition

Let $C$ assign a natural number to every position of an execution. Suppose that

- **C1:** if $i < j$ and the events at $i$ and $j$ belong to the same process, then $C(i) < C(j)$;
- **C2:** if $i < j$ and the event at $j$ receives the message sent by the event at $i$, then $C(i) < C(j)$.

Then $C$ satisfies the clock condition: if $a$ happened before $b$ then $C(a) < C(b)$.

This is Lamport's observation on p. 560 ("the Clock Condition is satisfied if the following two conditions hold"), for an arbitrary system of clocks. No clock algorithm is involved; the [Lamport timestamps](timestamps.md) are one clock satisfying C1 and C2.

## Background

- [Happened-before](happens-before.md): the proof is an induction on the chain of steps.

## Sources

- L. Lamport, *Time, Clocks, and the Ordering of Events in a Distributed System*, Communications of the ACM 21(7), July 1978, 558–565: "Logical Clocks", Clock Condition and conditions C1, C2, p. 560.
