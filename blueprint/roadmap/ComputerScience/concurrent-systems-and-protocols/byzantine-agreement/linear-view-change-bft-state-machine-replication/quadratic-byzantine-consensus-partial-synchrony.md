# The quadratic lower bound is tight for Byzantine consensus under partial synchrony

Under partial synchrony with $n \ge 3f + 1$ processes, authenticated channels and threshold signatures, there are deterministic Byzantine consensus (and state machine replication) protocols whose worst-case communication after GST is $O(n^2)$ words per decision, matching the Dolev–Reischuk lower bound $\Omega(n^2)$; in particular a single decision requires at most $O(n^2)$ messages even when up to $f$ consecutive leaders are faulty.

## Proof sketch

Combine a HotStuff-style linear protocol for each view with a view-synchronization mechanism whose worst-case cost over the at most $f + 1$ views needed to reach a correct leader is $O(n^2)$ in total: views are grouped into epochs of $f + 1$ views, synchronization messages are sent only at epoch boundaries, and within an epoch replicas advance views locally using timers; each epoch boundary costs $O(n^2)$ and after GST at most one epoch is needed.

## Depends on

- [Byzantine fault-tolerant state machine replication under partial synchrony](byzantine-state-machine-replication.md)
- [Quorum certificate from threshold signatures](quorum-certificate-threshold-signatures.md)

## Proof depends on

- [Byzantine agreement requires quadratic communication](dolev-reischuk-quadratic-lower-bound.md)
- [Expected linear communication for Byzantine view synchronization](expected-linear-view-synchronization.md)
- [Chained HotStuff with locking and three-phase commit](hotstuff-protocol-three-phase.md)

## Sources

- P. Civit, S. Gilbert, V. Gramoli, R. Guerraoui, J. Komatovic, "As Easy as ABC: Optimal (A)ccountable (B)yzantine (C)onsensus is Easy", IPDPS 2022.
- A. Lewis-Pye, "Quadratic worst-case message complexity for State Machine Replication in the partial synchrony model", arXiv:2201.01107 (2022).
