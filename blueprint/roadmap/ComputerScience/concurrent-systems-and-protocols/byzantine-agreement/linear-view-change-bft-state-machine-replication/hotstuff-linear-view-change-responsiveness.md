# HotStuff achieves optimistic responsiveness and linear view change

Call a view $v$ after GST *synchronized* if its leader is correct and all correct replicas remain in $v$ together for at least a bounded period $T_f$. GST bounds message delays but does not by itself put the correct replicas in the same view; that hypothesis is supplied by the protocol's view synchronization (for instance exponential back-off of view timeouts). In Basic HotStuff, a decision is reached in every synchronized view (Theorem 4). The correct leader of a synchronized view drives that decision with $O(n)$ authenticators of communication, including the view change, so after GST, if each view is synchronized once its leader is correct, the communication to decide following a sequence of $f$ faulty leaders is $O(f n)$ authenticators; and the protocol is optimistically responsive: in a synchronized view the leader proceeds after receiving $n - f$ messages, at the speed of the actual network delay rather than the bound $\delta$. Chained HotStuff pipelines the phases, each view's quorum certificate advancing the blocks of earlier views, and commits a block only when it heads a three-chain of direct-parent links; a run of consecutive synchronized views with correct leaders is therefore sufficient for a chained commit, but not necessary, since a faulty leader may also follow the protocol. In contrast, PBFT-style view changes with two-phase commit require $\Omega(n^2)$ authenticators (or $O(n^3)$ without threshold signatures) per view change.

## Proof sketch

Within a synchronized view, all correct replicas vote in every phase once the leader proposes, so the leader collects $n - f$ votes per phase within $T_f$. Each phase consists of one leader broadcast carrying a constant-size QC and $n$ votes sent back to the leader, i.e. $O(n)$ messages of constant size. The third phase is what removes the need for the new leader to justify its proposal with $n - f$ certificates. If the highest lock held by any replica is $\mathit{precommitQC}^*$, then at least $f + 1$ correct replicas voted for a matching $\mathit{prepareQC}^*$ and report it in their new-view messages (Lemma 3), so among any $n - f$ new-view messages the leader learns a prepare QC at least as high as the highest lock, not necessarily strictly higher, and uses it as its high QC. Every correct replica then accepts the proposal: if its lock has the same view as this QC, the lock matches it and the proposal extends the locked node (safety rule); if its lock is lower, possibly on a conflicting node, the QC has a strictly higher view (liveness rule).

## Depends on

- [Chained HotStuff with locking and three-phase commit](hotstuff-protocol-three-phase.md)
- [Byzantine fault-tolerant state machine replication under partial synchrony](byzantine-state-machine-replication.md)

## Proof depends on

- [Safety of HotStuff under n at least 3f + 1](hotstuff-safety.md)

## Sources

- M. Yin, D. Malkhi, M. K. Reiter, G. Golan Gueta, I. Abraham, "HotStuff: BFT Consensus with Linearity and Responsiveness", PODC 2019, arXiv:1803.05069, Section 4 (Algorithms 1 and 2, Lemma 3, Theorem 4) and Section 5.
