# Happened-before

Lamport's happened-before relation on the positions of an execution is
the transitive closure of one step of happened-before: $a$ happened before $b$ when there is a
chain $a = i_0, i_1, \dots, i_k = b$ with $k \ge 1$ in which each $i_m$ precedes $i_{m+1}$ by
one step.

This is Lamport's definition (p. 559) of the smallest relation containing process order and message order and closed under transitivity, on the positions of one finite execution.

## Background

- [One step of happened-before](step.md): the generating relation.

## Sources

- L. Lamport, *Time, Clocks, and the Ordering of Events in a Distributed System*, Communications of the ACM 21(7), July 1978, 558–565: "The Partial Ordering", Definition, p. 559.
