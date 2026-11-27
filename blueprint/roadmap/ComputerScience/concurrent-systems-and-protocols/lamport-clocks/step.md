# One step of happened-before

In an execution, position $i$ precedes position $j$ by one
step when $i < j$, both positions hold events, and either the two events belong to the same
process or the event at $j$ receives the message of the event at $i$.

## Sources

- L. Lamport, *Time, Clocks, and the Ordering of Events in a Distributed System*, Communications of the ACM 21(7), July 1978, 558–565: "The Partial Ordering", Definition, conditions (1) and (2), p. 559.
