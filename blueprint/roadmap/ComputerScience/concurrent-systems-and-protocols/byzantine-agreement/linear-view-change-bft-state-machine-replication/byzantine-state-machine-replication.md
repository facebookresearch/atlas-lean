# Byzantine fault-tolerant state machine replication under partial synchrony

A system has $n$ replicas, at most $f$ of which are Byzantine, communicating over authenticated point-to-point channels in the partial synchrony model: there is an unknown global stabilization time $\mathrm{GST}$ after which every message between correct replicas arrives within a known bound $\delta$. Clients submit commands; each correct replica outputs an infinite sequence (log) of commands. State machine replication (SMR) requires safety: the logs of any two correct replicas are prefixes of one another; and liveness: every command submitted by a correct client is eventually in the log of every correct replica. Communication complexity counts authenticators (signatures or signature shares) or words sent by correct replicas per committed decision.

## Depends on

- [Partial synchrony](../../distributed-execution-models/partial-synchrony.md)
- [Fail-stop, omission and Byzantine faults](../../distributed-execution-models/fail-stop-omission-and-byzantine-faults.md)

## Sources

- C. Dwork, N. Lynch, L. Stockmeyer, "Consensus in the Presence of Partial Synchrony", Journal of the ACM 35(2) (1988).
- M. Castro, B. Liskov, "Practical Byzantine Fault Tolerance and Proactive Recovery", ACM Transactions on Computer Systems 20(4) (2002); OSDI 1999.
