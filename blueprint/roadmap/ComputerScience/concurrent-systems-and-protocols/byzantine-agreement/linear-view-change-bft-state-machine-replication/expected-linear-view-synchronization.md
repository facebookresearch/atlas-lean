# Expected linear communication for Byzantine view synchronization

In the partial synchrony model with $n \ge 3f + 1$ replicas, there is a view synchronization protocol (bringing all correct replicas into a common view with a correct leader for long enough) whose expected communication complexity after GST is $O(n)$ words per synchronized view and whose expected latency is constant, assuming the adversary chooses the faulty set statically and leaders are chosen randomly. Combined with HotStuff, this gives Byzantine state machine replication with expected $O(n)$ communication per decision after GST.

## Proof sketch

Rather than broadcasting at every view advance, replicas send view-advance messages only to a small set of relays (the next leaders), which aggregate $f + 1$ messages into a threshold certificate and broadcast it once. Since faulty relays occur with probability at most $1/3$ per view under random leader selection, an expected constant number of relay attempts suffices, each costing $O(n)$.

## Depends on

- [Byzantine fault-tolerant state machine replication under partial synchrony](byzantine-state-machine-replication.md)
- [Chained HotStuff with locking and three-phase commit](hotstuff-protocol-three-phase.md)

## Proof depends on

- [HotStuff achieves optimistic responsiveness and linear view change](hotstuff-linear-view-change-responsiveness.md)
- [Quorum certificate from threshold signatures](quorum-certificate-threshold-signatures.md)

## Sources

- O. Naor, I. Keidar, "Expected Linear Round Synchronization: The Missing Link for Linear Byzantine SMR", DISC 2020, arXiv:2002.07539.
