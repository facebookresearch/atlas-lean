# Release of the lock requested at a position

For a locked schedule $s$ and a position $q$:
if $s$ has at position $q$ a lock request (in either mode) by transaction $t$ on item $x$, then
there is a position $r$ with $q < r$ and $r$ less than the length of $s$ at which $s$ has a release
by $t$ of $x$. If position $q$ holds a read, a write or a release, or lies beyond the end of $s$,
the condition holds trivially.
