# Dissemination, masking and opaque Byzantine quorum systems

A *quorum system* over a finite set $U$ of servers is a family of subsets (quorums). Against an adversary corrupting at most $b$ servers, a uniform threshold quorum system is a *dissemination* quorum system if every two quorums intersect in at least $b + 1$ servers and some quorum avoids every possible faulty set; a *masking* quorum system if every two quorums intersect in at least $2b + 1$ servers and some quorum avoids every faulty set; and an *opaque* quorum system if in addition intersections dominate the possibly faulty members of a quorum by the required margins.

## Depends on

- [Quorum system](../../paxos-consensus/quorum-system.md)
- [Fail-stop, omission and Byzantine faults](../../distributed-execution-models/fail-stop-omission-and-byzantine-faults.md)

## Sources

- Dahlia Malkhi and Michael Reiter, "Byzantine Quorum Systems", Distributed Computing, 1998.
