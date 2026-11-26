# States of two-phase commit with crashes

For a set $P$ of participants, a state of
two-phase commit with crashes is a global state of the protocol together with whether the
coordinator is operational and, for each participant $p \in P$, whether $p$ is operational. Each
process keeps its own state in its log on stable storage, so a crash does not change it.
