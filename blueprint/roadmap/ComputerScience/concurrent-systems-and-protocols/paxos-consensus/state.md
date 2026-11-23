# State of the single-decree Paxos algorithm

A state of single-decree Paxos, for a set $A$ of acceptors and a set $V$ of values, consists of: the set of numbers of the prepare requests sent; for each acceptor, the number of the highest prepare request it responded to, if any; the set of sent promises $(a, n, r)$, responses of acceptor $a$ to the prepare request $n$ reporting $r$ (nothing or a pair $(c, w) \in \mathbb{N} \times V$); the set of issued proposals $(n, v) \in \mathbb{N} \times V$ (accept requests); and the set of acceptances $(a, n, v)$, acceptor $a$ accepted the proposal $(n, v)$.

## Sources

- L. Lamport, *Paxos Made Simple*, ACM SIGACT News 32(4), December 2001, 51–58; author's version dated 01 Nov 2001: Section 2.2.
