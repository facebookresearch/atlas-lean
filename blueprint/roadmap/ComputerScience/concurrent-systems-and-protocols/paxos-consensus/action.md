# Actions of single-decree Paxos

Let $A$ be a set of acceptors and $V$ a set of values. The actions of single-decree Paxos, the labels of its transition system, are: $\mathrm{prepare}(n)$ for $n \in \mathbb{N}$ (send the prepare request $n$); $\mathrm{promise}(a, n, r)$ for $a \in A$, $n \in \mathbb{N}$ and $r$ either nothing or a pair $(c, w) \in \mathbb{N} \times V$ (acceptor $a$ answers the prepare request $n$, reporting $r$); $\mathrm{propose}(n, v, S)$ for $v \in V$ and a finite set $S \subseteq A$ (issue the proposal $(n, v)$, justified by the responses of the quorum $S$); and $\mathrm{accept}(a, n, v)$ (acceptor $a$ accepts the proposal $(n, v)$). Their effects are given by the [steps](step.md).

## Sources

- L. Lamport, *Paxos Made Simple*, ACM SIGACT News 32(4), December 2001, 51–58; author's version dated 01 Nov 2001: Section 2.2.
