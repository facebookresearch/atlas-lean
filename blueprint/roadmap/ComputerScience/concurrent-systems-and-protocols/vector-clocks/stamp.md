# Vector clock stamp of an event

Let $P$ be the set of processes. Given the current
vectors $V_q \in \mathbb{N}^P$ of the processes $q$ and the timestamps $T_0, T_1, \dots$ assigned
so far, the vector clock algorithm stamps an event $e$ of process $p$ as follows. Let $m = T_i$
if $e$ receives the message sent by the event at position $i$ and $T_i$ has been assigned, and
$m = 0$ otherwise. The stamp of $e$ is the pointwise maximum of $V_p$ and $m$, with its $p$-entry
increased by $1$.
