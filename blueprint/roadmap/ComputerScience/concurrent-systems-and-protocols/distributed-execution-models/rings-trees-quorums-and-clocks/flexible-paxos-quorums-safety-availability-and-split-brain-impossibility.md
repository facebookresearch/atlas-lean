# Flexible Paxos quorums: safety, availability and split-brain impossibility

Single-decree Paxos (Synod) with crash-stop acceptors is safe (at most one value is chosen, and only a proposed value) whenever every prepare quorum intersects every accept quorum, even if quorums of the same phase are disjoint. With cardinality thresholds $q_P, q_A$ on $n$ acceptors such a quorum system exists iff $q_P + q_A > n$. Conversely, split brain cannot be avoided without a majority: with fail-stop faults, synchronous processors and partially synchronous communication, no $t$-resilient consensus protocol on $2 \le n \le 2t$ processes achieves weak unanimity for binary values, because two disjoint groups of at most $t$ processes each, cut off from each other while messages between them are delayed, must each decide alone and can decide differently (Dwork, Lynch and Stockmeyer, Theorem 4.3). Without a sole leader the protocol can livelock: with three acceptors and two duelling proposers there is a crash-free, loss-free infinite execution in which no value is ever chosen; with a sole leader at a fresh highest ballot and live quorums, a value is chosen.

## Proof sketch

The safety invariant only needs that the prepare quorum of a higher ballot meets the accept quorum that chose a value, so the proposer learns it. For thresholds, two sets of sizes $q_P$ and $q_A$ must intersect iff $q_P + q_A > n$. The split-brain bound is the partition argument of the page on consensus under partial synchrony. For livelock, alternate the two proposers' prepare phases so each preempts the other's accept phase.

## Depends on

- [Single-decree Paxos as a labelled transition system](../../paxos-consensus/lts.md)
- [Quorum system](../../paxos-consensus/quorum-system.md)
- [Partial synchrony](../partial-synchrony.md)
- [Fail-stop, omission and Byzantine faults](../fail-stop-omission-and-byzantine-faults.md)

## Proof depends on

- [Paxos safety: at most one value is chosen](../../paxos-consensus/chosen-unique-of-can-reach.md)
- [Consensus under partial synchrony needs a majority](../../consensus-and-agreement/consensus-under-partial-synchrony-needs-a.md)

## Sources

- Heidi Howard, Dahlia Malkhi and Alexander Spiegelman, "Flexible Paxos: Quorum Intersection Revisited", 20th International Conference on Principles of Distributed Systems (OPODIS 2016), LIPIcs 70, 2017, §4.2 and §5, Theorems 1 and 2.
- Cynthia Dwork, Nancy Lynch and Larry Stockmeyer, "Consensus in the Presence of Partial Synchrony", Journal of the ACM 35(2), 1988, §4.3, Theorem 4.3.
- Leslie Lamport, "The Part-Time Parliament", ACM Transactions on Computer Systems, 1998.
- Leslie Lamport, "Paxos Made Simple", ACM SIGACT News, 2001.
