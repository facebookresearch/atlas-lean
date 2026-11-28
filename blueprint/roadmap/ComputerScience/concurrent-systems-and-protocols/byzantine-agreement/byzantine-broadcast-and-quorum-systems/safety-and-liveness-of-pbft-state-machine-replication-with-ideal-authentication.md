# Safety and liveness of PBFT state machine replication with ideal authentication

Consider Practical Byzantine Fault Tolerance with $n > 3f$ replicas, at most $f$ of them faulty, certificates (quorums) of $q$ matching messages from distinct replicas where $2q - n \ge f + 1$, so that any two quorums share at least $f + 1$ replicas, and $q \le n - f$, so that the correct replicas alone form a quorum (for instance $q = \lceil (n + f + 1)/2 \rceil$, which is $2f + 1$ when $n = 3f + 1$), views with a rotating primary, the three-phase normal case (pre-prepare, prepare, commit) per sequence slot, and view changes carrying prepared certificates, under ideal authentication. Then prepared certificates for a slot and view are unique, a value committed locally at a slot by a correct replica is the only value that can be prepared at that slot in any higher view, and hence correct replicas never commit different requests at the same slot and their executed state-machine prefixes agree. For $n = 3f + 1$ and $q = 2f + 1$, Castro and Liskov also prove liveness through the view-change protocol rather than within a single view: correct clients eventually receive replies to their requests, provided at most $f$ replicas are faulty and $\mathrm{delay}(t)$, the time from the moment $t$ at which a message is first sent until it is received when its sender keeps retransmitting it, does not grow faster than $2^t$ indefinitely (Castro and Liskov, Section 3). With $n = 3$, $f = 1$ and quorums of size $n - f = 2$, which violates $2q - n \ge f + 1$, a split-brain execution violates agreement. The safety statements for general $n > 3f$ and the $n = 3$ counterexample are derived here from the quorum-intersection argument; Castro and Liskov treat $n = 3f + 1$.

## Proof sketch

Any two quorums intersect in at least $f + 1$ replicas, one of them correct, which prepares at most one value per slot and view. A view change collects a quorum of messages, one of which comes from a correct replica holding the committed certificate, forcing the new primary to re-propose that value.

## Depends on

- [Dissemination, masking and opaque Byzantine quorum systems](dissemination-masking-and-opaque-byzantine-quorum-systems.md)
- [Partial synchrony](../../distributed-execution-models/partial-synchrony.md)

## Proof depends on

- [Cardinality conditions for threshold Byzantine quorum systems and masking-register safety](cardinality-conditions-for-threshold-byzantine-quorum-systems-and-masking-regist.md)

## Sources

- Miguel Castro and Barbara Liskov, "Practical Byzantine Fault Tolerance", Proceedings of the Third Symposium on Operating Systems Design and Implementation (OSDI '99), 1999, Sections 2, 3 (the liveness guarantee and its synchrony assumption) and 4.2–4.5 (the liveness argument in Section 4.5.2).
- Miguel Castro and Barbara Liskov, "Practical Byzantine Fault Tolerance and Proactive Recovery", ACM Transactions on Computer Systems, 2002.
