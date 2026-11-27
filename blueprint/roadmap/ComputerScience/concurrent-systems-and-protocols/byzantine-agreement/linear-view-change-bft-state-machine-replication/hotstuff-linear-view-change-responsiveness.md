# HotStuff achieves optimistic responsiveness and linear view change

Call a view $v$ after GST *synchronized* if its leader is correct and all correct replicas remain in $v$ together for at least a bounded period $T_f$. GST bounds message delays but does not by itself put the correct replicas in the same view; that hypothesis is supplied by the protocol's view synchronization (for instance exponential back-off of view timeouts). In Basic HotStuff, a decision is reached in every synchronized view (Theorem 4). The correct leader of a synchronized view drives that decision with $O(n)$ authenticators of communication, including the view change, so after GST, if each view is synchronized once its leader is correct, the communication to decide following a sequence of $f$ faulty leaders is $O(f n)$ authenticators; and the protocol is optimistically responsive: in a synchronized view the leader proceeds after receiving $n - f$ messages, at the speed of the actual network delay rather than the bound $\delta$. Chained HotStuff pipelines the phases, each view's quorum certificate advancing the blocks of earlier views, and commits a block only when it heads a three-chain, three blocks certified in consecutive views; a commit there therefore needs a run of consecutive synchronized views with correct leaders, not a single one. In contrast, PBFT-style view changes with two-phase commit require $\Omega(n^2)$ authenticators (or $O(n^3)$ without threshold signatures) per view change.

## Proof sketch

Within a synchronized view, all correct replicas vote in every phase once the leader proposes, so the leader collects $n - f$ votes per phase within $T_f$. Each phase consists of one leader broadcast carrying a constant-size QC and $n$ votes sent back to the leader, i.e. $O(n)$ messages of constant size. The third phase is what removes the need for the new leader to justify its proposal with $n - f$ certificates: a replica locked on a block can be convinced by a single higher QC, because the extra phase guarantees that a QC higher than any lock exists among the $n - f$ new-view messages, so the leader waits only for those messages.

## Depends on

- [Chained HotStuff with locking and three-phase commit](hotstuff-protocol-three-phase.md)
- [Byzantine fault-tolerant state machine replication under partial synchrony](byzantine-state-machine-replication.md)

## Proof depends on

- [Safety of HotStuff under n at least 3f + 1](hotstuff-safety.md)

## Sources

- M. Yin, D. Malkhi, M. K. Reiter, G. Golan Gueta, I. Abraham, "HotStuff: BFT Consensus with Linearity and Responsiveness", PODC 2019, arXiv:1803.05069.
