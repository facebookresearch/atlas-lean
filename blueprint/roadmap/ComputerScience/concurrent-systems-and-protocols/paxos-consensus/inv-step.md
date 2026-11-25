# Every step of single-decree Paxos preserves the invariant

Let $Q$ be a quorum system. If a state satisfies the [inductive invariant](inv.md) for $Q$, so does the state after any [step](step.md) for $Q$. The two delicate cases are these.

- A *promise* by acceptor $a$ for number $n$ is the first response of $a$ to the prepare request $n$, since earlier responses were for numbers at most its previous highest prepare number, which is below $n$. So the value rule of every issued proposal, which quantifies over the responses of its quorum for its own number, is unaffected.
- An *acceptance* by $a$ of a proposal numbered $n$ requires $n$ to be at least every prepare number $a$ has responded to (rule P1a), so it does not change the highest acceptance of $a$ below any of those numbers: past reports stay truthful. This is where acceptors' promises enter.

## Background

- [Highest-numbered acceptance below a number](highest-below.md): the report an acceptor sends, and why it stays truthful.

## Sources

- L. Lamport, *Paxos Made Simple*, ACM SIGACT News 32(4), December 2001, 51–58; author's version dated 01 Nov 2001: Section 2.2, rule P1a and Phases 1 and 2.
