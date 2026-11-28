# Byzantine agreement

Byzantine agreement (consensus with Byzantine faults) in the sense of Fischer, Lynch and Merritt: every process has an input, and the correct processes must decide the same value, which must be their common input when they all have the same one. The model on these pages is synchronous (lock-step rounds), with Byzantine failures (a faulty process may send anything to anyone, differently to each recipient), on a complete network of reliable links on which a receiver knows the sender of every message, without signatures. No deterministic protocol reaches Byzantine agreement when $2 \le n \le 3m$, where $n$ is the number of processes and $m$ the number of faults.

- [Synchronous Byzantine agreement protocol](agreement-protocol.md)
- [Executions of a Byzantine agreement protocol](state.md)
- [Decision of a process in Byzantine agreement](decision.md)
- [Agreement condition of Byzantine agreement](agreement.md)
- [Validity condition of Byzantine agreement](validity.md)
- [Reaching Byzantine agreement](solves.md)
- [No synchronous protocol reaches Byzantine agreement when $3 \le n \le 3m$](not-solves-of-card-le-three-mul.md)
- [No synchronous protocol for three processes reaches Byzantine agreement with one fault](not-solves-three.md)
- [No synchronous protocol for two processes reaches Byzantine agreement with one fault](not-solves-of-card-eq-two.md)
- [No synchronous protocol reaches Byzantine agreement when $2 \le n \le 3m$](not-solves-of-two-le-card.md)
- [Byzantine generals from Byzantine agreement](to-oral.md)
- [Order carried by a first-round message](order-of.md)
- [Protocol message carried by a later message](msg-of.md)
- [Later messages of the commander protocol](to-oral-send-succ.md)
- [Later rounds of the commander protocol](to-oral-recv-succ.md)
- [The commander protocol simulates the agreement protocol](state-to-oral.md)
- [Byzantine agreement yields the Byzantine generals problem](solves-to-oral.md)
- [Bounds for Synchronous Byzantine Agreement](byzantine-agreement-bounds/README.md)
- [Byzantine Broadcast and Quorum Systems](byzantine-broadcast-and-quorum-systems/README.md)
- [Asynchronous Byzantine Agreement and DAG-Based Atomic Broadcast](asynchronous-byzantine-agreement-and-dag-protocols/README.md)
- [Linear View-Change BFT State Machine Replication](linear-view-change-bft-state-machine-replication/README.md)

## Related topics

- [Byzantine generals problem](../byzantine-generals-problem/README.md): the commander version (one general sends an order), to which the impossibility here is reduced.
- [FLP impossibility](../flp-impossibility/README.md): consensus with crash faults in an asynchronous system, impossible already with one fault.
- [Synchronous consensus with crash failures](../synchronous-consensus-with-crash-failures/README.md): the same synchronous rounds with the milder crash failures, where the bound is on the number of rounds.
