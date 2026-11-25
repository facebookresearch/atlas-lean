# Sorting a list by exactly k signed reversals

For natural numbers $k$ and $n$ and a list of integers $\pi$, the statement "$\pi$ sorts to
$(1, \dots, n)$ in exactly $k$ signed reversals" is defined inductively:

- the identity list $(1, 2, \dots, n)$ sorts in $0$ signed reversals;
- if $\pi$ has length $m$, $i \le j < m$, and the [signed reversal](srev-block.md)
  $\operatorname{rev}^{\pm}_{i,j}(\pi)$ of positions $i$ to $j$ sorts in $k$ signed reversals,
  then $\pi$ sorts in $k + 1$ signed reversals.

Thus $\pi$ sorts in exactly $k$ signed reversals when $k$ signed reversals applied in turn, each of
a block of positions $i \le j$ inside the current list, turn $\pi$ into $(1, \dots, n)$, with every
entry positive (Shamir and Peer, Lecture 11, signed setting). A one-entry signed reversal ($i = j$)
changes one sign, and only the identity list sorts in $0$ signed reversals.
