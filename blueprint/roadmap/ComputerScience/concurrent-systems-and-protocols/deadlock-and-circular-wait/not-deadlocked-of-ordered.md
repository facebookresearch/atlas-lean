# Resource ordering prevents deadlock

Let $\mathrm{rank}$ assign a natural number to
each resource. If a resource-allocation snapshot with finitely many processes is ordered by
$\mathrm{rank}$ (Havender's discipline), that is, $\mathrm{rank}(r') < \mathrm{rank}(r)$
whenever some process requests $r$ and holds $r'$, then no set of processes is deadlocked.
