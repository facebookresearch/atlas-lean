# Strictness at a pair of positions

For a locked schedule $s$ and positions $p$ and $q$: if
$s$ has at position $p$ a release by transaction $t$ of item $x$, just before position $p$
transaction $t$ holds an exclusive lock on $x$, and $s$ has at position $q$ a read or write by
$t$, then $q < p$. For every other pair of positions, including positions beyond the end of $s$,
the condition holds trivially.
