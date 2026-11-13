# Every reported process is stuck

Let $w$ be the free resource vector. For every process $q$
that the detection algorithm reports, the request of $q$ is not at most $w$ plus the sum of the
allocations of the processes that the algorithm lets finish: for at least one resource type, $q$
requests more than is free even after all those processes have released their allocations.
