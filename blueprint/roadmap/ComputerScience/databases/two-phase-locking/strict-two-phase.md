# Strict two-phase schedules

A locked schedule $s$ is strict two-phase when it is two-phase
and every transaction releases its exclusive locks only after its last read or write: whenever
$s$ has at position $p$ a release by transaction $t$ of item $x$ and just before position $p$
transaction $t$ holds an exclusive lock on $x$, every read or write of $t$ in $s$ occurs at a
position before $p$.
