# One step of the Lamport clock algorithm

The state is a counter $c(p) \in \mathbb{N}$
for each process $p$ together with the timestamps assigned so far. An event $e$ of process
$p$ gets the timestamp $t = \max(c(p), s) + 1$, where $s$ is the timestamp already assigned
at the position that $e$ receives from; $s = 0$ if $e$ is not a receipt or if no timestamp
has been assigned at that position. The step sets $c(p)$ to $t$ and appends $t$ to the
timestamps.

The timestamps are kept in an array, for constant-time append and lookup.
