# Lamport's P2b

In every [Paxos voting history](voting.md): if the proposal numbered $m$ with value $v$ is chosen, then every proposal issued with a number $n > m$ has value $v$.

**Proof.** Lamport's induction on $n$ (Section 2.2). Let $C$ be a quorum that accepted $(m, v)$, and let $S$ be the quorum that P2c gives for the proposal $(n, w)$. The two quorums share an acceptor $a$, which accepted a proposal numbered $m < n$, so $S$ did accept proposals below $n$; by P2c, $w$ is then the value of a proposal accepted by $S$ at some number $c < n$ with no acceptance by $S$ strictly between $c$ and $n$. Since $a$ accepted at $m$, $m \le c$. If $c = m$, uniqueness of proposal numbers gives $w = v$; if $m < c$, the induction hypothesis applied to the proposal numbered $c$ gives $w = v$.

## Informally uses

- [Quorum system](quorum-system.md): the intersection of $C$ and $S$.

## Background

- [A Paxos voting history](voting.md): the conditions P2c, unique numbers and acceptance of issued proposals.

## Sources

- L. Lamport, *Paxos Made Simple*, ACM SIGACT News 32(4), December 2001, 51–58; author's version dated 01 Nov 2001: Section 2.2, P2b and the derivation of P2c.
