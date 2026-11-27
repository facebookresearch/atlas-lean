# Synchronous Byzantine state machine replication with minority faults and 2-delta commit latency

In the synchronous model with message delay bound $\Delta$ (and actual delay $\delta \le \Delta$), with $n \ge 2f + 1$ replicas and digital signatures, there is a leader-based Byzantine state machine replication protocol (Sync HotStuff) that is safe and live. In the steady state of a view with a correct leader, a proposal is committed by every correct replica within time $2\Delta + O(\delta)$ after it is proposed, and correct replicas vote and certify at actual network speed between commits; this is a steady-state latency, not a bound that holds across view changes, which take additional time. A replica votes only for a valid proposal: one carrying a certificate for the block it extends, received from the leader or forwarded by another replica, with no leader equivocation detected in the view.

## Proof sketch

Each replica forwards a valid proposal, votes for it immediately and starts a $2\Delta$ commit timer; if no equivocation by the leader is detected before the timer expires, the replica commits the block and its ancestors. Any conflicting proposal by a Byzantine leader is forwarded by some correct replica within $\Delta$ and reaches everyone before the others' timers expire, so no two correct replicas commit conflicting blocks; $f + 1$ votes form a certificate since every certificate contains a correct replica's vote. A replica quits a view upon $f + 1$ blame messages or proof of equivocation; it then stops voting in that view and aborts all of that view's outstanding commit timers, waits $\Delta$, locks on a highest certified block and sends it to the next leader. The new leader waits $2\Delta$ and proposes extending a highest certified block it knows, and a replica casts its first vote in the new view only if that block ranks at least as high as its lock.

## Depends on

- [Byzantine fault-tolerant state machine replication under partial synchrony](byzantine-state-machine-replication.md)

## Sources

- I. Abraham, D. Malkhi, K. Nayak, L. Ren, M. Yin, "Sync HotStuff: Simple and Practical Synchronous State Machine Replication", IEEE Symposium on Security and Privacy 2020, Figures 1 and 2, Theorem 3.
