# The inductive invariant of single-decree Paxos

Let $Q$ be a quorum system. A [state](state.md) of single-decree Paxos satisfies the inductive invariant for $Q$ when:

- every acceptance $(a, b, v)$ is of an issued proposal $(b, v)$;
- proposal numbers are unique: two issued proposals with the same number have the same value;
- an acceptor $a$ that responded to the prepare request $n$ has a highest prepare number $k$ with $n \le k$;
- the report $r$ of every response $(a, n, r)$ is still the [highest-numbered acceptance](highest-below.md) of $a$ below $n$;
- every issued proposal $(n, v)$ is justified: some quorum $S$ of $Q$ has every acceptor responded to the prepare request $n$, and $v$ satisfies [Lamport's value rule](safe-value.md) for $S$ and $n$.

## Sources

- L. Lamport, *Paxos Made Simple*, ACM SIGACT News 32(4), December 2001, 51–58; author's version dated 01 Nov 2001: Section 2.2.
