# One round of pointer jumping on arrays

Given an array $P$ of pointers (each a node
among $0, \dots, n-1$ or undefined) and an array $S$ of sums in an additive monoid $M$, one
round returns arrays $P'$ and $S'$ of length $n$ where, for each node $v$: if $P[v]$ is
undefined, then $P'[v]$ is undefined and $S'[v] = S[v]$; if $P[v] = u$, then $P'[v] = P[u]$ and
$S'[v] = S[v] + S[u]$. A read outside an array gives an undefined pointer or the sum $0$.
