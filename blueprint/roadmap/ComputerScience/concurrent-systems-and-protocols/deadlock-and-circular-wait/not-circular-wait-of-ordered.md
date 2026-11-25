# Resource ordering prevents circular wait

Let $\mathrm{rank}$ assign a natural number
to each resource. If a resource-allocation snapshot is ordered by $\mathrm{rank}$ (Havender's
discipline), that is, $\mathrm{rank}(r') < \mathrm{rank}(r)$ whenever some process requests
$r$ and holds $r'$, then the snapshot has no circular wait: no process waits for itself
through a chain of one or more wait-for edges.
