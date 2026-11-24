# At most one value is chosen

In every [Paxos voting history](voting.md), for any quorum system, two chosen values are equal: the second safety requirement of Section 2.1, "Only a single value is chosen".

If the two values are chosen at numbers $m \le n$, they are equal when $m = n$ by uniqueness of proposal numbers (a quorum is nonempty, so a chosen proposal was issued), and when $m < n$ by [Lamport's P2b](p2b.md).

## Informally uses

- [Lamport's P2b](p2b.md): the case of different proposal numbers.

## Sources

- L. Lamport, *Paxos Made Simple*, ACM SIGACT News 32(4), December 2001, 51–58; author's version dated 01 Nov 2001: Section 2.1 (safety requirements) and Section 2.2 ("Since numbers are totally ordered, condition P2 guarantees the crucial safety property that only a single value is chosen").
