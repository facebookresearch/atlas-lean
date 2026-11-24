# Solutions survive AC-3

Let $P$ be a binary constraint satisfaction problem with
finitely many variables and $\mathrm{dom}$ finite domains for its variables. If $\sigma$ is a
solution of $P$ within $\mathrm{dom}$, then for every variable $v$ the value $\sigma(v)$ lies in
the domain of $v$ returned by AC-3 run from $\mathrm{dom}$ with all arcs of $P$ queued.
