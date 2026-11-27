# Happened-before is irreflexive

No event happened before itself: for every execution and every position $a$, it is not the case that $a$ happened before $a$.

Lamport assumes this (p. 559: "We assume that a ↛ a for any event a"). In this model of a finite execution it is a theorem, since happened-before only goes forward in the list; the statement is the same, but here it is derived rather than assumed.

## Informally uses

- [Happened-before goes forward in the execution](lt.md): irreflexivity follows from $a < a$ being false.

## Sources

- L. Lamport, *Time, Clocks, and the Ordering of Events in a Distributed System*, Communications of the ACM 21(7), July 1978, 558–565: "The Partial Ordering", p. 559.
