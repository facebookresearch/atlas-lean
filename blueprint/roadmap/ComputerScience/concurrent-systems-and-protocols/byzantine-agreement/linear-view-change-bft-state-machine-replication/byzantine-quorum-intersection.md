# Quorums of size n - f intersect in a correct replica when n is at least 3f + 1

Let $n \ge 3f + 1$ replicas include at most $f$ Byzantine ones. Any two sets $Q_1, Q_2$ of replicas with $\lvert Q_1 \rvert, \lvert Q_2 \rvert \ge n - f$ intersect in at least $f + 1$ replicas, hence in at least one correct replica. Consequently, if a correct replica votes for at most one value per view and phase, two conflicting values cannot both collect quorum certificates of $n - f$ votes in the same view and phase.

## Proof sketch

By inclusion-exclusion $\lvert Q_1 \cap Q_2 \rvert \ge 2(n - f) - n = n - 2f \ge f + 1$. Since at most $f$ replicas are Byzantine, some replica in the intersection is correct; a correct replica that voted for one value in a given view and phase did not vote for another, so two quorum certificates for different values in the same view and phase are impossible.

## Depends on

- [Byzantine fault-tolerant state machine replication under partial synchrony](byzantine-state-machine-replication.md)
- [Quorum certificate from threshold signatures](quorum-certificate-threshold-signatures.md)

## Sources

- M. Castro, B. Liskov, "Practical Byzantine Fault Tolerance and Proactive Recovery", ACM Transactions on Computer Systems 20(4) (2002); OSDI 1999.
- M. Yin, D. Malkhi, M. K. Reiter, G. Golan Gueta, I. Abraham, "HotStuff: BFT Consensus with Linearity and Responsiveness", PODC 2019, arXiv:1803.05069.
