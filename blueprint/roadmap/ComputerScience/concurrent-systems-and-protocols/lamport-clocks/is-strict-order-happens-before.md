# Happened-before is an irreflexive partial order

In every execution, happened-before is irreflexive and transitive, that is, a strict partial order on the positions of the execution. Lamport, p. 559: "This implies that → is an irreflexive partial ordering on the set of all events in the system."

Concurrent events are the distinct pairs that this order does not compare; executions with concurrent events exist, for instance two events of different processes, neither of which receives a message.

## Informally uses

- [Happened-before is irreflexive](happens-before-irrefl.md): the irreflexivity half.

## Sources

- L. Lamport, *Time, Clocks, and the Ordering of Events in a Distributed System*, Communications of the ACM 21(7), July 1978, 558–565: "The Partial Ordering", p. 559.
