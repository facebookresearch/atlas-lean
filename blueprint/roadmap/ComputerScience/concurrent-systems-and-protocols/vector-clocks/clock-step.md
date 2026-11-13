# One step of the vector clock algorithm

The state of the algorithm holds a vector
$V_q \in \mathbb{N}^P$ for each process $q$, where $P$ is the set of processes, and the
timestamps assigned so far, kept in an array for constant-time append and lookup. On an event $e$
of process $p$, the step replaces $V_p$ by the stamp $s$ of $e$ computed from the current state,
leaves the other vectors unchanged, and appends $s$ to the timestamps.
