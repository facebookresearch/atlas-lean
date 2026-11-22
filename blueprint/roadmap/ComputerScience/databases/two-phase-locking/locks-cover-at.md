# Lock coverage at a position

For a locked schedule $s$ and a position $p$: if $s$ has at
position $p$ a read or write $o$ by transaction $t$ on item $x$, then just before position $p$
transaction $t$ holds a lock on $x$ whose mode covers the mode $o$ requires (shared for a read,
exclusive for a write; an exclusive lock covers both modes). If position $p$ holds a lock request
or a release, or lies beyond the end of $s$, the condition holds trivially.
