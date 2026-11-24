# Paxos safety: at most one value is chosen

Let $Q$ be a quorum system. In every state reachable from the initial state of [single-decree Paxos](lts.md) for $Q$, two [chosen values](value-chosen.md) are equal. Acceptances are never withdrawn, so a value chosen once stays chosen, and no other value is chosen later in the same run.

This is the second safety requirement of Section 2.1, for the algorithm of Section 2.2 with the acceptor response of step 1(b) (p. 4), in the asynchronous non-Byzantine model, with any quorum system (majorities in the paper). It is not about the unbounded response of the Phase 1(b) summary on p. 5 (see [Paxos consensus](README.md)). For a quorum system with at least one quorum and a nonempty set of values, a state in which a value is chosen is reachable (one prepare request, answered by a quorum reporting nothing, then one proposal accepted by that quorum), so the theorem is not vacuous.

## Informally uses

- [Reachable states are Paxos voting histories](voting-of-inv.md): every reachable state is a voting history.
- [The Paxos invariant holds in every reachable state](inv-of-can-reach.md): the invariant behind it.
- [At most one value is chosen](chosen-unique.md): the voting argument.

## Sources

- L. Lamport, *Paxos Made Simple*, ACM SIGACT News 32(4), December 2001, 51–58; author's version dated 01 Nov 2001: Sections 2.1 and 2.2.
