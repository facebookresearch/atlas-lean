# Counting jobs when every machine is heavily loaded

Let $\sigma$ be a schedule of a list
$P$ of jobs on $m$ machines, let $p$ and $M$ be natural numbers, and let $d = \max(M - p, 0)$. If
every job in $P$ is at least $p$ and every machine has load (the sum of its jobs) greater than
$d$, then $2m \le n + k$, where $n$ is the number of jobs in $P$ and $k$ is the number of jobs
$x$ in $P$ with $p \le x$ and $x > d$, both counted with multiplicity.

The reason is that each machine then holds two jobs or one job longer than $d$.
