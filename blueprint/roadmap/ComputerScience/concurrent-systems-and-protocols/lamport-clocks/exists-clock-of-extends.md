# Every total order extending happened-before comes from a clock system

Let $e_0, \dots, e_{n-1}$ be an execution and let $r$ be a relation on positions that is irreflexive, transitive, total on the positions $0, \dots, n-1$, and contains happened-before. Then there is a clock $C$ that satisfies the clock condition and whose [induced order](clock-before.md) is exactly $r$ on the positions $0, \dots, n-1$ (and relates nothing else).

Lamport states this without proof on p. 561: "Given any total ordering relation ⇒ which extends →, there is a system of clocks satisfying the Clock Condition which yields that relation." The clock here is the rank of a position in $r$: the number of positions below it. It never ties, so the order on processes plays no role. It is a clock system in Lamport's abstract sense; it is generally not produced by the [clock algorithm](timestamps.md). Conversely, for every clock satisfying the clock condition the induced order [extends happened-before](clock-before-of-happens-before.md) and [is total](clock-before-total.md). Together these show that the total orders induced by clocks satisfying the clock condition are exactly the strict total orders on the events that extend happened-before.

The hypotheses are satisfiable: the order of positions in the list, and Lamport's own total order, both qualify, and they disagree on two concurrent events.

## Background

- [The clock condition](clock-condition.md): the property the constructed clock satisfies.
- [Linear extensions of posets](../../../Combinatorics/partially-ordered-sets/linear-extensions-of-posets/README.md): the orders $r$ in question are the linear extensions of happened-before.

## Sources

- L. Lamport, *Time, Clocks, and the Ordering of Events in a Distributed System*, Communications of the ACM 21(7), July 1978, 558–565: "Ordering the Events Totally", p. 561.
