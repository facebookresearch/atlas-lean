# Lamport clocks

Lamport's logical clocks (1978). Happened-before is the causal order of the events of a distributed system: the smallest transitive relation containing the order of events within a process and the order from the sending of a message to its receipt. A system of clocks satisfies the clock condition when it gives every event a larger number than the events that happened before it; Lamport's implementation rules IR1 and IR2 give such clocks, and breaking ties between processes turns their values into a total order that extends happened-before.

**Model.** One finite execution, given as a list of events in an order consistent with causality (an interleaving); each event belongs to a process and may receive the message of one earlier event, named by its position, and every event may send. Process order is the list order restricted to one process.

- *Synchrony:* none. Only the order of events matters; no physical clocks, no bounds on speeds or delays.
- *Failures:* none modelled (Lamport's 1978 analysis of logical clocks assumes none).
- *Messages:* a receipt refers to the event that sent the message; messages may be received out of order and need not be received at all. Lamport's mutual-exclusion algorithm in the same paper additionally assumes FIFO, reliable channels.

In this model happened-before is an irreflexive partial order by construction (an event only happens before later positions), whereas Lamport assumes irreflexivity.

## Happened-before

- [Event](event.md)
- [Well-formed executions](well-formed.md)
- [One step of happened-before](step.md)
- [Happened-before](happens-before.md)
- [Happened-before goes forward in the execution](lt.md)
- [Happened-before is irreflexive](happens-before-irrefl.md)
- [Happened-before is an irreflexive partial order](is-strict-order-happens-before.md)
- [Happened-before relates positions of the execution](exists-events.md)

## Clocks and the clock condition

- [Conditions C1 and C2 imply the clock condition](clock-condition-of-c1-c2.md)
- [One step of the Lamport clock algorithm](clock-step.md)
- [Running the Lamport clock algorithm](run.md)
- [Lamport timestamps](timestamps.md)
- [Appending events does not change earlier timestamps](timestamps-append.md)
- [Process counters dominate their timestamps](timestamp-le-clock.md)
- [A timestamp depends only on a prefix containing its event](timestamps-get-d-take.md)
- [One step of happened-before raises the timestamp](step-lt.md)
- [A receipt is stamped later than its send](timestamp-lt-of-recv.md)
- [Lamport timestamps increase along each process](timestamp-lt-of-proc.md)
- [The clock condition](clock-condition.md)

## The total order

- [The order induced by a clock system](clock-before.md)
- [The order induced by a clock satisfying the clock condition extends happened-before](clock-before-of-happens-before.md)
- [The order induced by a clock satisfying the clock condition is total](clock-before-total.md)
- [Lamport's total order](total-before.md)
- [Lamport's total order is the order induced by the Lamport timestamps](total-before-eq-clock-before.md)
- [Lamport's total order extends happened-before](total-before-of-happens-before.md)
- [Lamport's order is total](total-before-total.md)
- [Every total order extending happened-before comes from a clock system](exists-clock-of-extends.md)

## Related topics

- [Vector clocks](../vector-clocks/README.md): the same execution model; vector timestamps characterise happened-before exactly, which Lamport timestamps cannot, since the converse of the clock condition fails.
- [Linear extensions of posets](../../../Combinatorics/partially-ordered-sets/linear-extensions-of-posets/README.md): Lamport's total order is a linear extension of happened-before, and every linear extension arises from some clock system.
- [Paxos consensus](../paxos-consensus/README.md): Lamport's state-machine approach needs a total order of commands; Paxos, run once per command (*Paxos Made Simple*, Section 3), provides one despite crash failures.
- [Bakery algorithm](../bakery-algorithm/README.md): the shared-memory counterpart, which breaks ties between equal tickets by process name, as the total order here breaks ties between equal clock values.

## Sources

- L. Lamport, *Time, Clocks, and the Ordering of Events in a Distributed System*, Communications of the ACM 21(7), July 1978, 558–565: "The Partial Ordering" (definition of →, p. 559), "Logical Clocks" (Clock Condition, C1, C2, IR1, IR2, p. 560), "Ordering the Events Totally" (the relation ⇒, p. 561).
