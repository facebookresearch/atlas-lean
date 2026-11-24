# Schedule of a computation DAG

A schedule of a computation DAG on $n$ tasks on $p$
processors assigns to each task $v$ a step $t(v) \in \mathbb{N}$ in which it runs, such that
$t(u) < t(v)$ whenever $u$ is a predecessor of $v$, and for every step $s$ at most $p$ tasks $v$
have $t(v) = s$.
