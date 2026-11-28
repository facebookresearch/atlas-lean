# Synchronous Byzantine state machine replication with minority faults and 2-delta commit latency

In the synchronous model with message delay bound $\Delta$ (and actual delay $\delta \le \Delta$), with $n \ge 2f + 1$ replicas and digital signatures, there is a leader-based Byzantine state machine replication protocol (Sync HotStuff) that is safe and live. In the steady state of a view with a correct leader, a proposal is committed by every correct replica within time $2\Delta + O(\delta)$ after it is proposed, and correct replicas vote and certify at actual network speed between commits; this is a steady-state latency, not a bound that holds across view changes, which take additional time. A certificate for a block is a set of $f + 1$ signed votes on it from one view. At each height of a view, a replica votes for the first valid proposal it receives for that height, from the leader or through another replica's vote, if the proposed block extends a highest certified block known to it (certified blocks being ranked first by view, then by height).

## Proof sketch

In the steady state (Figure 1) the leader proposes a block extending the highest certified block it knows; a replica that votes for a block forwards the proposal, starts a $2\Delta$ commit timer, and commits the block and its ancestors when the timer expires. In the view change (Figure 2) a replica blames the leader if fewer than $p$ blocks arrive from it within $(2p+1)\Delta$ time, or on receiving two equivocating blocks; on gathering $f + 1$ blame messages it broadcasts them and quits the view, aborting all its commit timers and no longer voting in that view, then waits $\Delta$, enters the next view and sends a highest certified block to the new leader. For safety, suppose a correct replica $r$ votes for $B_l$ at time $t$ and commits it at $t + 2\Delta$. Its vote, which acts as a re-proposal, reaches every correct replica by $t + \Delta$; a correct replica that had already voted for an equivocating block, or quit the view, before then would have let $r$ see this before $t + 2\Delta$. So every correct replica votes for $B_l$, no equivocating block is certified in that view (every certificate contains a correct replica's vote), and every correct replica holds the certificate of $B_l$ before entering the next view (Lemma 1). Since leaders propose, and replicas vote for, only blocks extending a highest certified block, induction on views shows that every certified block of higher rank extends $B_l$ (Lemma 2), so correct replicas never commit different blocks at the same height (Theorem 3).

## Depends on

- [Byzantine fault-tolerant state machine replication under partial synchrony](byzantine-state-machine-replication.md)

## Sources

- I. Abraham, D. Malkhi, K. Nayak, L. Ren, M. Yin, "Sync HotStuff: Simple and Practical Synchronous State Machine Replication", IEEE Symposium on Security and Privacy 2020, Section III: Figures 1 and 2, Lemmas 1 and 2, Theorem 3.
