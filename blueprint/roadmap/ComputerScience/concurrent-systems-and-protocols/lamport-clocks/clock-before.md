# The order induced by a clock system

Fix a linear order on the processes and a clock $C$ assigning a natural number to each position of an execution. Position $a$ precedes position $b$ when both hold events and either $C(a) < C(b)$, or $C(a) = C(b)$ and the process of $a$ is smaller than the process of $b$.

This is Lamport's relation ⇒ (p. 561), defined for any system of clocks; with the Lamport timestamps as $C$ it is [Lamport's total order](total-before.md).

## Sources

- L. Lamport, *Time, Clocks, and the Ordering of Events in a Distributed System*, Communications of the ACM 21(7), July 1978, 558–565: "Ordering the Events Totally", p. 561.
