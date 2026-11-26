# Safety and liveness of PBFT state machine replication with ideal authentication

Consider Practical Byzantine Fault Tolerance with $n > 3f$ replicas, quorums large enough that any two intersect in at least $f + 1$ replicas (size $2f + 1$ when $n = 3f + 1$), views with a rotating primary, the three-phase normal case (pre-prepare, prepare, commit) per sequence slot, and view changes carrying prepared certificates, under ideal authentication. Then prepared certificates for a slot and view are unique, a value committed locally at a slot by a correct replica is the only value that can be prepared at that slot in any higher view, and hence correct replicas never commit different requests at the same slot and their executed state-machine prefixes agree. In a view with a correct primary and timely delivery, every submitted request is committed after the three phases. With $n = 3$, $f = 1$ and quorums of size $n - f = 2$, a split-brain execution violates agreement.

## Proof sketch

Any two quorums intersect in at least $f + 1$ replicas, one of them correct, which prepares at most one value per slot and view. A view change collects a quorum of messages, one of which comes from a correct replica holding the committed certificate, forcing the new primary to re-propose that value.

## Depends on

- [Dissemination, masking and opaque Byzantine quorum systems](dissemination-masking-and-opaque-byzantine-quorum-systems.md)
- [Partial synchrony](../../distributed-execution-models/partial-synchrony.md)

## Proof depends on

- [Cardinality conditions for threshold Byzantine quorum systems and masking-register safety](cardinality-conditions-for-threshold-byzantine-quorum-systems-and-masking-regist.md)

## Sources

- Miguel Castro and Barbara Liskov, "Practical Byzantine Fault Tolerance", Proceedings of the Third Symposium on Operating Systems Design and Implementation (OSDI '99), 1999.
- Miguel Castro and Barbara Liskov, "Practical Byzantine Fault Tolerance and Proactive Recovery", ACM Transactions on Computer Systems, 2002.
