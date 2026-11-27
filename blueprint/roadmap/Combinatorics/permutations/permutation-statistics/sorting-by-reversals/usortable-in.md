# Sorting a list by exactly k reversals

For natural numbers $k$ and $n$ and a list of integers $\pi$, the statement "$\pi$ sorts to
$(1, \dots, n)$ in exactly $k$ reversals" is defined inductively:

- the identity list $(1, 2, \dots, n)$ sorts in $0$ reversals;
- if $\pi$ has length $m$, $i \le j < m$, and the [reversal](rev-block.md)
  $\operatorname{rev}_{i,j}(\pi)$ of positions $i$ to $j$ sorts in $k$ reversals, then $\pi$
  sorts in $k + 1$ reversals.

Thus $\pi$ sorts in exactly $k$ reversals when $k$ reversals applied in turn, each of a block of
positions $i \le j$ inside the current list, turn $\pi$ into $(1, \dots, n)$ (Shamir and Peer,
Lecture 11, §11.2). A one-entry reversal ($i = j$) leaves the list unchanged but counts as a step,
and only the identity list sorts in $0$ reversals.
