# Dijkstra–Scholten termination detection for diffusing computations

In an asynchronous diffusing computation started by a root process, the Dijkstra–Scholten overlay has each process track its deficit (unacknowledged basic messages it has sent) and a parent pointer to the process whose message engaged it; a process acknowledges non-engaging messages immediately and detaches (acknowledging its parent) when it is passive with zero deficit. In every reachable state, each process's deficit equals its in-flight basic messages plus acknowledgements owed to it, the engaged processes form a tree rooted at the root, and the root detects termination only when the computation is globally quiescent (all processes passive, no messages in flight). Conversely, once the underlying computation stops, the overlay drains and the root detects termination.

## Proof sketch

Invariants by induction over transitions: deficits count outstanding messages and children, and parent pointers form a tree because a process gets a parent only when it is disengaged. If the root has zero deficit and is passive, the tree is empty, so every process is passive and no message is in flight. Liveness follows from a drain measure that strictly decreases once the computation is idle.

## Depends on

- [Asynchronous message-passing systems](../../distributed-execution-models/asynchronous-message-passing-systems.md)

## Sources

- Edsger W. Dijkstra and Carel S. Scholten, "Termination Detection for Diffusing Computations", Information Processing Letters, 1980.
- Friedemann Mattern, "Algorithms for Distributed Termination Detection", Distributed Computing, 1987.
