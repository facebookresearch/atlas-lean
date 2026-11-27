# Byzantine consensus under partial synchrony requires and suffices with n > 3t

In the basic round model of partial synchrony (arbitrary message loss before an unknown global stabilization round GST, reliable delivery among correct processes from GST on), for $n \ge 3t + 1$ Dwork, Lynch and Stockmeyer's Algorithm 3 solves deterministic unauthenticated Byzantine consensus with consistency, strong unanimity and termination for an arbitrary value domain (Theorem 3.3). It runs in trying phases owned in rotation by the processes, with value locking, Srikanth–Toueg broadcast, proposals backed by $n - t$ accepted lists and decisions on $2t + 1$ acknowledgments, and all correct processes decide by round $\mathrm{GST} + 6(n + 1)$ (the bound stated after Theorem 3.3). Conversely, for $2 \le n \le 3t$ no $t$-resilient consensus protocol achieves weak unanimity for binary values when communication is partially synchronous, even with authentication and synchronous processors (Theorem 4.4), so the minimum number of processes for $t$-resilient unauthenticated Byzantine consensus under partial synchrony is $3t + 1$ (Table I).

## Proof sketch

Safety: a decision rests on $2t + 1$ acknowledgments, so at least $t + 1$ correct processes lock the decided value, and since a proposal needs $n - t$ processes to find its value acceptable, no conflicting value can be proposed in a later phase. Liveness: the trying phase of a correct owner that follows a lock-release phase, both at or after GST, ends in a decision. Impossibility for $n \le 3t$ partitions the processes into three groups of at most $t$ and delays messages between two of them past the decision times of two runs in which the third group is faulty or dead.

## Depends on

- [Partial synchrony](../../distributed-execution-models/partial-synchrony.md)
- [Resilient consensus protocols](../../consensus-and-agreement/resilient-consensus-protocols.md)
- [Fail-stop, omission and Byzantine faults](../../distributed-execution-models/fail-stop-omission-and-byzantine-faults.md)

## Proof depends on

- [Consensus under partial synchrony with benign faults](../../consensus-and-agreement/consensus-under-partial-synchrony-with-benign.md)
- [No synchronous protocol reaches Byzantine agreement when $3 \le n \le 3m$](../not-solves-of-card-le-three-mul.md)

## Sources

- Cynthia Dwork, Nancy Lynch and Larry Stockmeyer, "Consensus in the Presence of Partial Synchrony", Journal of the ACM 35(2), 1988, Table I, §3.2.3 (Algorithm 3, Theorem 3.3), Theorem 4.4.
