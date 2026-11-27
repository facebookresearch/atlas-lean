# A Paxos voting history

A Paxos voting history, for a [quorum system](quorum-system.md) on a set $A$ of acceptors and a set $V$ of values, consists of two relations: $\mathrm{proposed}(b, v)$, a proposal numbered $b \in \mathbb{N}$ with value $v$ was issued, and $\mathrm{voted}(a, b, v)$, acceptor $a$ accepted it. They must satisfy:

- **unique numbers:** different proposals have different numbers ($\mathrm{proposed}(b, v)$ and $\mathrm{proposed}(b, w)$ imply $v = w$);
- **acceptance of issued proposals:** $\mathrm{voted}(a, b, v)$ implies $\mathrm{proposed}(b, v)$;
- **P2c:** for every issued proposal $(b, v)$ there is a quorum $S$ such that either (a) no acceptor of $S$ accepted a proposal numbered less than $b$, or (b) for some $c < b$ an acceptor of $S$ accepted a proposal $(c, v)$ and no acceptor of $S$ accepted anything numbered strictly between $c$ and $b$; that is, $v$ is the value of the highest-numbered proposal below $b$ accepted by $S$.

Lamport states P2c for the acceptances made before the proposal is issued. Here it is required of the whole history, the form in which his algorithm maintains it: an acceptor that answered the prepare request $b$ promised never to accept below $b$ afterwards ([Reachable states are Paxos voting histories](voting-of-inv.md)). No timing, failure or message assumption enters this definition.

## Sources

- L. Lamport, *Paxos Made Simple*, ACM SIGACT News 32(4), December 2001, 51–58; author's version dated 01 Nov 2001: Section 2.2 (unique proposal numbers, P2c).
