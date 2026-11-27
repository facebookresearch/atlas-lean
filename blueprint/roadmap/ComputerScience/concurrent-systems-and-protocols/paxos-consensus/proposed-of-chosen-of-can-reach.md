# Paxos safety: only a proposed value is chosen

Let $Q$ be a quorum system. In every state reachable from the initial state of [single-decree Paxos](lts.md) for $Q$, a [chosen value](value-chosen.md) is the value of some issued proposal: the first safety requirement of Section 2.1.

## Informally uses

- [Reachable states are Paxos voting histories](voting-of-inv.md)
- [Only a proposed value is chosen](proposed-of-chosen.md)

## Sources

- L. Lamport, *Paxos Made Simple*, ACM SIGACT News 32(4), December 2001, 51–58; author's version dated 01 Nov 2001: Section 2.1.
