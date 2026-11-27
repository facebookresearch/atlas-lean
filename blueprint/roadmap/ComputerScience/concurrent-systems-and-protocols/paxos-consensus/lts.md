# Single-decree Paxos as a labelled transition system

Single-decree Paxos, for a [quorum system](quorum-system.md), is the labelled transition system whose states are [Paxos states](state.md), whose labels are [actions](action.md) and whose transitions are the [steps](step.md). A state is reachable when finitely many steps lead to it from the [initial state](init.md).

## Sources

- L. Lamport, *Paxos Made Simple*, ACM SIGACT News 32(4), December 2001, 51–58; author's version dated 01 Nov 2001: Section 2.2.
