# Reachable states are Paxos voting histories

Let $Q$ be a quorum system. In every state of [single-decree Paxos](lts.md) satisfying the [inductive invariant](inv.md) for $Q$, the issued proposals and the acceptances form a [Paxos voting history](voting.md). In particular P2c holds over the whole history: the quorum that justified a proposal under [Lamport's value rule](safe-value.md) witnesses it, because the reports of its acceptors are still their highest acceptances below the proposal number.

## Background

- [The inductive invariant of single-decree Paxos](inv.md): truthful reports and justified proposals.

## Sources

- L. Lamport, *Paxos Made Simple*, ACM SIGACT News 32(4), December 2001, 51–58; author's version dated 01 Nov 2001: Section 2.2 (P2c and how Phase 1 maintains it).
