# Highest-numbered acceptance below a number

Let $\mathit{votes}$ be a set of acceptances $(a, c, w)$ (acceptor $a$ accepted the proposal numbered $c$ with value $w$), $a$ an acceptor and $n \in \mathbb{N}$. A report $r$ is the highest-numbered acceptance of $a$ below $n$ in $\mathit{votes}$ when either $r$ is nothing and $a$ accepted no proposal numbered less than $n$, or $r = (c, w)$ with $c < n$, $(a, c, w) \in \mathit{votes}$, and $a$ accepted no proposal numbered $d$ with $c < d < n$.

## Sources

- L. Lamport, *Paxos Made Simple*, ACM SIGACT News 32(4), December 2001, 51–58; author's version dated 01 Nov 2001: Section 2.2.
