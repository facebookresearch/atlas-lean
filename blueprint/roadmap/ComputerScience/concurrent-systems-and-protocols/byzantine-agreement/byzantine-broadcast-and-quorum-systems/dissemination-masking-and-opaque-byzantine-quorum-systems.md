# Dissemination, masking and opaque Byzantine quorum systems

A *quorum system* over a finite set $U$ of servers is a family of subsets (quorums). Against an adversary corrupting at most $b$ servers, so that the possible faulty sets are the sets $B \subseteq U$ with $|B| \le b$, a quorum system is a *dissemination* quorum system if every two quorums intersect in at least $b + 1$ servers (equivalently, $Q_1 \cap Q_2 \not\subseteq B$ for all quorums $Q_1, Q_2$ and every possible faulty set $B$); a *masking* quorum system if every two quorums intersect in at least $2b + 1$ servers (equivalently, $(Q_1 \cap Q_2) \setminus B_1 \not\subseteq B_2$ for all quorums $Q_1, Q_2$ and possible faulty sets $B_1, B_2$); and a *$b$-opaque* quorum system if for all quorums $Q_1, Q_2$ and every set $B$ of at most $b$ servers both $|(Q_1 \cap Q_2) \setminus B| \ge |(Q_2 \cap B) \cup (Q_2 \setminus Q_1)|$ and $|(Q_1 \cap Q_2) \setminus B| > |Q_2 \cap B|$ hold. Each of the three notions also requires availability: for every set $B$ of at most $b$ servers some quorum is disjoint from $B$. These are the threshold cases of Malkhi and Reiter's D-Consistency and D-Availability (Definition 5.1), M-Consistency and M-Availability (Definition 4.1), and O-Consistency1, O-Consistency2 and O-Availability (Definition 5.9). The non-strict inequality in O-Consistency1 is deliberate: with it, for $n = |U|$ and $b > 0$, all quorums of size $\lceil (2n + 2b)/3 \rceil$ form a $b$-opaque system whenever $n \ge 5b$ (Example 5.11), and a $b$-opaque system exists iff $n \ge 5b$ (Theorem 5.12).

## Depends on

- [Quorum system](../../paxos-consensus/quorum-system.md)
- [Fail-stop, omission and Byzantine faults](../../distributed-execution-models/fail-stop-omission-and-byzantine-faults.md)

## Sources

- Dahlia Malkhi and Michael Reiter, "Byzantine Quorum Systems", Distributed Computing 11, 1998, Definitions 4.1, 5.1 and 5.9, Example 5.11 and Theorem 5.12.
