# The Paxos invariant holds in every reachable state

Let $Q$ be a quorum system. Every state reachable from the [initial state](init.md) of [single-decree Paxos](lts.md) for $Q$ satisfies the [inductive invariant](inv.md) for $Q$: the invariant holds initially and is preserved by every step, so induction on the number of steps gives it in every reachable state.

## Informally uses

- [The Paxos invariant holds initially](inv-init.md)
- [Every step of single-decree Paxos preserves the invariant](inv-step.md)

## Sources

- L. Lamport, *Paxos Made Simple*, ACM SIGACT News 32(4), December 2001, 51–58; author's version dated 01 Nov 2001: Section 2.2.
