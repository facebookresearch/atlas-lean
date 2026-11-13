# Two-phase condition at a pair of positions

For a locked schedule $s$ and positions $p$ and
$q$: if $s$ has at position $p$ a release by transaction $t$ and at position $q$ a lock request by
the same transaction $t$, then $q < p$. For every other pair of positions, including positions
beyond the end of $s$, the condition holds trivially.
