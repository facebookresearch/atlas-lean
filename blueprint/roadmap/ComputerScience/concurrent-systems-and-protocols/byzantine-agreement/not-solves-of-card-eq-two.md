# No synchronous protocol for two processes reaches Byzantine agreement with one fault

If there are exactly two processes and at least two values, no deterministic synchronous protocol reaches Byzantine agreement with at most $m \ge 1$ faulty processes, in any number of rounds.

**Proof.** Give the processes different inputs $v \ne w$ and consider the run with no fault. If the second process is faulty and sends exactly what it sends in that run, the first cannot tell the two runs apart; being the only correct process, it must decide its own input $v$ (validity), so it decides $v$ in the fault-free run too. Symmetrically the second decides $w$ there, contradicting agreement.

**Relation to the sources.** Fischer, Lynch and Merritt assume throughout that graphs have at least three nodes, so this case is outside their Theorem 1; the argument here is an elementary indistinguishability argument, not taken from a cited source. The model is the one of [Synchronous Byzantine agreement protocol](agreement-protocol.md).

## Background

- [No synchronous protocol reaches Byzantine agreement when $3 \le n \le 3m$](not-solves-of-card-le-three-mul.md): the case of three or more processes.

## Sources

- M. J. Fischer, N. A. Lynch, M. Merritt, *Easy impossibility proofs for distributed consensus problems*, Distributed Computing 1(1), 1986, 26–39: Theorem 1 (stated for at least three nodes).
