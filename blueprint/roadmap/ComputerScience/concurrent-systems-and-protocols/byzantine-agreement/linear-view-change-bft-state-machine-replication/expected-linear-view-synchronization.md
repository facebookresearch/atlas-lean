# Expected linear communication for Byzantine view synchronization

In the partial synchrony model with $n \ge 3f + 1$ replicas, a PKI and threshold signatures, there is a round (view) synchronization protocol, bringing all correct replicas into a common round with a correct leader for long enough, whose relays and leaders are chosen by a random function of the round. Against a static oblivious adversary, which fixes the faulty set in advance and has no knowledge of this randomness, the expected latency and the expected communication until the next synchronization after GST are constant and $O(n)$ words, respectively, in the worst case over all reachable states and adversary behaviours. Against a strong static adversary, which may know the randomness, the same bounds hold only on average over the synchronization events of an infinite run. Combined with HotStuff, this gives Byzantine state machine replication with expected $O(n)$ communication per decision after GST, with the same quantifier over adversaries.

## Proof sketch

Rather than broadcasting at every round advance, replicas send their wish to advance only to the current relay of the round. The relay aggregates $f + 1$ such messages into a threshold signature and broadcasts a pre-commit message, $f + 1$ wishes ensuring that at least one correct replica wants to advance; once $2f + 1$ replicas commit to the round, the relay broadcasts a commit certificate, so that at least $f + 1$ correct replicas know of the intent, and after $2f + 1$ finalize messages the round is entered and lagging replicas are helped. A replica that sees no progress moves on to the next of the round's $f + 1$ relays. Since relays are chosen at random, independently of the oblivious adversary's static choice of faulty replicas, an expected constant number of relay attempts suffices, each costing $O(n)$ words.

## Depends on

- [Byzantine fault-tolerant state machine replication under partial synchrony](byzantine-state-machine-replication.md)
- [Chained HotStuff with locking and three-phase commit](hotstuff-protocol-three-phase.md)

## Proof depends on

- [HotStuff achieves optimistic responsiveness and linear view change](hotstuff-linear-view-change-responsiveness.md)
- [Quorum certificate from threshold signatures](quorum-certificate-threshold-signatures.md)

## Sources

- O. Naor, I. Keidar, "Expected Linear Round Synchronization: The Missing Link for Linear Byzantine SMR", DISC 2020, arXiv:2002.07539, Sections 2, 3 and 5 (Section 5.5 for the strong adversary).
