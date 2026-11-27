# Chandy–Lamport snapshots detect stable properties and always complete

For an asynchronous FIFO message-passing system, a predicate on global states is *stable* if it remains true along every transition once true. If the Chandy–Lamport marker algorithm runs from a pre-snapshot state to a completed snapshot, then for every stable predicate: if it holds in the recorded global state it holds in the actual state at completion, and if it fails in the recorded state it failed at the start. Moreover, on a strongly connected (for example complete) network, every fair infinite execution of the marker-augmented system in which some process initiates eventually records every local state and every channel state.

## Proof sketch

The recorded state is reachable from the initial state and reaches the final state, by permuting pre- and post-recording events, so stable predicates transfer forwards. Liveness: markers propagate along every edge under fairness, and strong connectivity carries them from the initiator to every process.

## Depends on

- [Correctness of the Chandy–Lamport snapshot algorithm](../../distributed-execution-models/correctness-of-the-chandylamport-snapshot.md)
- [Consistent cuts and their lattice](../../distributed-execution-models/consistent-cuts-and-their-lattice.md)
- [Weak and strong fairness](../../distributed-execution-models/weak-and-strong-fairness.md)

## Sources

- K. Mani Chandy and Leslie Lamport, "Distributed Snapshots: Determining Global States of Distributed Systems", ACM Transactions on Computer Systems, 1985.
