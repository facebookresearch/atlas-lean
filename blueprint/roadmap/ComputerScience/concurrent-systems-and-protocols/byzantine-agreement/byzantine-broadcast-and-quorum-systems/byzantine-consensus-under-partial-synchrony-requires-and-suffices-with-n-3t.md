# Byzantine consensus under partial synchrony requires and suffices with n > 3t

In the basic round model of partial synchrony (arbitrary message loss before an unknown global stabilization round, reliable delivery among correct processes afterwards), deterministic unauthenticated Byzantine consensus with agreement, strong validity on correct inputs and termination is solvable if and only if $n > 3t$ (or $n \le 1$). For $n > 3t$ a rotating-coordinator protocol with view locking and quorums of size $n - t$ is safe in every run, regardless of synchrony, and every correct process decides by the end of the first view that starts after stabilization and has a correct coordinator, hence within $t + 1$ views after stabilization.

## Proof sketch

Safety: any two quorums of size $n - t$ share a correct process when $n > 3t$, so a locked value blocks conflicting decisions in later views. Liveness: after stabilization, a view with a correct coordinator completes. Impossibility for $n \le 3t$ follows by partitioning into three groups and using message loss before stabilization to simulate the synchronous covering argument.

## Depends on

- [Partial synchrony](../../distributed-execution-models/partial-synchrony.md)
- [Resilient consensus protocols](../../consensus-and-agreement/resilient-consensus-protocols.md)
- [Fail-stop, omission and Byzantine faults](../../distributed-execution-models/fail-stop-omission-and-byzantine-faults.md)

## Proof depends on

- [Consensus under partial synchrony with benign faults](../../consensus-and-agreement/consensus-under-partial-synchrony-with-benign.md)
- [No synchronous protocol reaches Byzantine agreement when $3 \le n \le 3m$](../not-solves-of-card-le-three-mul.md)

## Sources

- Cynthia Dwork, Nancy Lynch and Larry Stockmeyer, "Consensus in the Presence of Partial Synchrony", Journal of the ACM, 1988.
