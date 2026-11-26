# Synchronous Byzantine state machine replication with minority faults and 2-delta commit latency

In the synchronous model with message delay bound $\Delta$ (and actual delay $\delta \le \Delta$), with $n \ge 2f + 1$ replicas and digital signatures, there is a leader-based Byzantine state machine replication protocol (Sync HotStuff) that is safe and live, in which a correct leader's proposal is committed by every correct replica within time $2\Delta + O(\delta)$ after it is proposed, and in which correct replicas vote and certify at actual network speed between commits. For $n \le 2f$, Byzantine agreement, and hence state machine replication serving commands from all clients, is impossible even with signatures and synchrony, although Byzantine broadcast from a designated sender remains solvable.

## Proof sketch

Each replica votes for the leader's proposal immediately and starts a $2\Delta$ commit timer; if no equivocation by the leader is detected before the timer expires, the replica commits. Any conflicting proposal by a Byzantine leader is forwarded by some correct replica within $\Delta$ and reaches everyone before the others' timers expire, so no two correct replicas commit conflicting blocks; $f + 1$ votes form a certificate since every certificate contains a correct replica's vote. View changes forward the highest certified block so the next leader extends it.

## Depends on

- [Byzantine fault-tolerant state machine replication under partial synchrony](byzantine-state-machine-replication.md)
- [Reaching Byzantine agreement](../solves.md)

## Sources

- I. Abraham, D. Malkhi, K. Nayak, L. Ren, M. Yin, "Sync HotStuff: Simple and Practical Synchronous State Machine Replication", IEEE Symposium on Security and Privacy 2020.
