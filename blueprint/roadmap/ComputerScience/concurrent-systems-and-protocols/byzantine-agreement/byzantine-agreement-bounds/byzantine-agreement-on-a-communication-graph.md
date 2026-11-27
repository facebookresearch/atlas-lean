# Byzantine agreement on a communication graph

In the synchronous model on an undirected communication graph $G$, processes send messages only along edges. A deterministic protocol solves *Boolean Byzantine agreement* on $G$ against $t$ faults in $R$ rounds if, for every set of at most $t$ faulty processes injecting arbitrary messages on their incident edges, all correct processes decide the same bit after round $R$, and if all correct processes start with the same bit they decide it.

## Depends on

- [Reaching Byzantine agreement](../solves.md)
- [Fail-stop, omission and Byzantine faults](../../distributed-execution-models/fail-stop-omission-and-byzantine-faults.md)

## Sources

- Michael J. Fischer, Nancy A. Lynch and Michael Merritt, "Easy Impossibility Proofs for Distributed Consensus Problems", Proceedings of the Fourth Annual ACM Symposium on Principles of Distributed Computing, 1985.
- Danny Dolev, "The Byzantine Generals Strike Again", Journal of Algorithms, 1982.
