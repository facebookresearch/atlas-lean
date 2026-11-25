# Two-phase schedules

A locked schedule $s$ is two-phase when every lock request of a
transaction precedes every release of that transaction: whenever $s$ has at position $p$ a release
by transaction $t$ and at position $q$ a lock request by $t$ (on any items, in any mode), then
$q < p$.
