# The order induced by a clock satisfying the clock condition is total

Let $C$ be any clock on the positions of an execution that satisfies the clock condition, and fix a linear order on the processes. For any two distinct positions $a \ne b$ holding events, $a$ precedes $b$ or $b$ precedes $a$ in the [order induced by $C$](clock-before.md). Two events of the same process are related by happened-before, so the clock condition separates their clock values; ties between different processes are broken by the order on processes. The induced order is also irreflexive and transitive for every clock, so it is a strict total order on the events.

## Sources

- L. Lamport, *Time, Clocks, and the Ordering of Events in a Distributed System*, Communications of the ACM 21(7), July 1978, 558–565: "Ordering the Events Totally", p. 561 ("It is easy to see that this defines a total ordering").
