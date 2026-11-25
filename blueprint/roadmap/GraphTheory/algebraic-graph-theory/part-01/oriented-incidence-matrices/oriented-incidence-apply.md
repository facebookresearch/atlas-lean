# Entries of the oriented incidence matrix

Let $V$ and $E$ be sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$. The entry of the [oriented incidence matrix](oriented-incidence.md) at $(v, e)$ is $[e^- = v] - [e^+ = v]$, where $[P]$ is $1$ if $P$ holds and $0$ otherwise.

For a circuit, read $V$ as the nodes and $E$ as the branches, each branch running from its tail $e^-$ to its head $e^+$: the entry $A(n, e) = [\mathrm{tail}(e) = n] - [\mathrm{head}(e) = n]$ of the electrical incidence matrix is $+1$ at the tail, $-1$ at the head and $0$ at every other node, and $0$ at every node when tail and head coincide.
