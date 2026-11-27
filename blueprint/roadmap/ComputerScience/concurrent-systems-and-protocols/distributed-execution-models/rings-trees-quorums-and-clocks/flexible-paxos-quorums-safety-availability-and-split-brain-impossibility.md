# Flexible Paxos quorums: safety, availability and split-brain impossibility

Single-decree Paxos (Synod) with crash-stop acceptors is safe (at most one value is chosen, and only a proposed value) whenever every prepare quorum intersects every accept quorum, even if quorums of the same phase are disjoint. With cardinality thresholds $q_P, q_A$ on $n$ acceptors such a quorum system exists iff $q_P + q_A > n$. Conversely, any asynchronous quorum protocol that can make progress on two disjoint sets of processes is unsafe, so crash-tolerant consensus with progress on single quorums is impossible when $n \le 2t$. Without a sole leader the protocol can livelock: with three acceptors and two duelling proposers there is a crash-free, loss-free infinite execution in which no value is ever chosen; with a sole leader at a fresh highest ballot and live quorums, a value is chosen.

## Proof sketch

The safety invariant only needs that the prepare quorum of a higher ballot meets the accept quorum that chose a value, so the proposer learns it. For thresholds, two sets of sizes $q_P$ and $q_A$ must intersect iff $q_P + q_A > n$. For livelock, alternate the two proposers' prepare phases so each preempts the other's accept phase.

## Depends on

- [Single-decree Paxos as a labelled transition system](../../paxos-consensus/lts.md)
- [Quorum system](../../paxos-consensus/quorum-system.md)

## Proof depends on

- [Paxos safety: at most one value is chosen](../../paxos-consensus/chosen-unique-of-can-reach.md)

## Sources

- Heidi Howard, Dahlia Malkhi and Alexander Spiegelman, "Flexible Paxos: Quorum Intersection Revisited", 20th International Conference on Principles of Distributed Systems (OPODIS 2016), 2017.
- Leslie Lamport, "The Part-Time Parliament", ACM Transactions on Computer Systems, 1998.
- Leslie Lamport, "Paxos Made Simple", ACM SIGACT News, 2001.
