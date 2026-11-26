# An emptied domain rules out solutions

Let $P$ be a binary constraint satisfaction
problem with finitely many variables and $\mathrm{dom}$ finite domains for its variables. If AC-3,
run from $\mathrm{dom}$ with all arcs of $P$ queued, returns the empty domain for some variable
$v$, then no assignment $\sigma$ is a solution of $P$ within $\mathrm{dom}$.
