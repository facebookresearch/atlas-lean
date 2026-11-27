# Lamport's order is total

In every execution, for any two distinct positions $a \ne b$
that both hold events, $a$ precedes $b$ or $b$ precedes $a$ in Lamport's total order.

Two events of the same process have different timestamps (an earlier event of a process has
a smaller timestamp), so ties only occur between different processes, which the order on
processes breaks.

## Sources

- L. Lamport, *Time, Clocks, and the Ordering of Events in a Distributed System*, Communications of the ACM 21(7), July 1978, 558–565: "Ordering the Events Totally", p. 561 ("It is easy to see that this defines a total ordering").
