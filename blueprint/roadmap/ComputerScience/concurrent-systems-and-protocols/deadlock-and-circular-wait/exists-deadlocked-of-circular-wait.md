# Circular wait yields a deadlocked set

If a resource-allocation snapshot has
circular wait, that is, some process $p$ waits for itself through a chain of one or more
wait-for edges, then some set of processes is deadlocked.

One such set consists of the processes on a wait-for cycle through $p$.
