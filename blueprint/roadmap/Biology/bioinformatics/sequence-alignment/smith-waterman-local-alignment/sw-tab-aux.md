# Row-by-row filling of the Smith–Waterman table

For a sequence $y$, a sequence $x$, a current row $r$ and a running maximum $m$: if $x$ is empty the result is $\max(m, \mu(r))$; for $x = a x'$ it is the result for $x'$, the [next row](next-row.md) of $r$ for $a$ and $y$, and the running maximum $\max(m, \mu(r))$. Here $\mu(r) = \max(0, r_0, r_1, \dots)$ is the [floored maximum](../pairwise-sequence-alignment/list-max.md).
