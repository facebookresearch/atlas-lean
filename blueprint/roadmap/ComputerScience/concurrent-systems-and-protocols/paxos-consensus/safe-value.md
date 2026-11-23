# Lamport's value rule

Let $\mathit{promises}$ be a set of responses $(a, n, r)$ to prepare requests, $S$ a finite set of acceptors, $n \in \mathbb{N}$ and $v$ a value. The value $v$ satisfies Lamport's value rule (Phase 2(a)) for $S$ and $n$ when either every response of an acceptor of $S$ to the prepare request $n$ reports nothing, or some acceptor of $S$ responded to the prepare request $n$ reporting a proposal $(c, v)$ and every proposal $(c', w')$ reported by an acceptor of $S$ in response to the prepare request $n$ has $c' \le c$.

## Sources

- L. Lamport, *Paxos Made Simple*, ACM SIGACT News 32(4), December 2001, 51–58; author's version dated 01 Nov 2001: Section 2.2.
