# The order induced by a clock satisfying the clock condition extends happened-before

Let $C$ be any clock on the positions of an execution that satisfies the clock condition ($a$ happened before $b$ implies $C(a) < C(b)$). If $a$ happened before $b$, then $a$ precedes $b$ in the [order induced by $C$](clock-before.md). Lamport, p. 561: "the Clock Condition implies that if a → b then a ⇒ b". With the Lamport timestamps as $C$ this is [Lamport's total order extends happened-before](total-before-of-happens-before.md).

## Sources

- L. Lamport, *Time, Clocks, and the Ordering of Events in a Distributed System*, Communications of the ACM 21(7), July 1978, 558–565: "Ordering the Events Totally", p. 561.
