# No solution is lost

Let $P$ be a binary constraint satisfaction problem with finitely
many variables, $\mathrm{dom}$ finite domains for its variables, and $q$ a queue of arcs each of
which is an arc of $P$. Then every solution $\sigma$ of $P$ within $\mathrm{dom}$ is also a
solution of $P$ within the domains returned by AC-3 started from $\mathrm{dom}$ with queue $q$.
