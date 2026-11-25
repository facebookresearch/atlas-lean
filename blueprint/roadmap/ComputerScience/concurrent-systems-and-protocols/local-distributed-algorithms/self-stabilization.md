# Self-stabilization

In Dijkstra's setting, finite-state machines sit at the nodes of a connected graph; each machine has privileges, Boolean functions of its own state and its neighbours' states, and a central daemon repeatedly selects one present privilege, whose machine then moves to a new state determined by its old state, its neighbours' states and the selected privilege. A global predicate $L$ marks the legitimate states, required to satisfy: every legitimate state has a present privilege; every move from a legitimate state leads to a legitimate state; every privilege is present in some legitimate state; and any legitimate state can be reached from any other by moves. The system is *self-stabilizing* if, from every initial state and for every sequence of daemon selections, some privilege is always present and a legitimate state is reached after finitely many moves. Later formulations keep the two core conditions, closure of $L$ under steps and convergence to $L$ from every state under every execution the scheduler allows, for general schedulers.

## Depends on

- [Infinite run](../../process-calculi/labelled-transition-systems/omega-run.md)

## Sources

- E. W. Dijkstra, "Self-stabilizing systems in spite of distributed control", *Communications of the ACM* 17(11):643–644, 1974; transcription of the manuscript (EWD 426) in the E. W. Dijkstra Archive, <https://www.cs.utexas.edu/~EWD/transcriptions/EWD04xx/EWD426.html>
- S. Dolev, *Self-Stabilization*, MIT Press, 2000
