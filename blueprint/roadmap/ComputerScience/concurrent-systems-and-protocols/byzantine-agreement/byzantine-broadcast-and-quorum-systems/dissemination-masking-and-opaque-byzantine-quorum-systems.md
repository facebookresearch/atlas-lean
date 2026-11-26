# Dissemination, masking and opaque Byzantine quorum systems

A *quorum system* over a finite set $U$ of servers is a family of subsets (quorums). Against an adversary corrupting at most $b$ servers, a uniform threshold quorum system is a *dissemination* quorum system if every two quorums intersect in at least $b + 1$ servers and some quorum avoids every possible faulty set; a *masking* quorum system if every two quorums intersect in at least $2b + 1$ servers and some quorum avoids every faulty set; and a *$b$-opaque* quorum system if $|(Q_1 \cap Q_2) \setminus B| > |(Q_2 \cap B) \cup (Q_2 \setminus Q_1)|$ for all quorums $Q_1, Q_2$ and every set $B$ of at most $b$ servers, and some quorum avoids every faulty set.

## Depends on

- [Quorum system](../../paxos-consensus/quorum-system.md)
- [Fail-stop, omission and Byzantine faults](../../distributed-execution-models/fail-stop-omission-and-byzantine-faults.md)

## Sources

- Dahlia Malkhi and Michael Reiter, "Byzantine Quorum Systems", Distributed Computing, 1998.
