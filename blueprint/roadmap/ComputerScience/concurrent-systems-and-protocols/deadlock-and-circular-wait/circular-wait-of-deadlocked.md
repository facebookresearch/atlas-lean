# A deadlocked set forces circular wait

In a resource-allocation snapshot with
finitely many processes, if some set of processes is deadlocked, then the snapshot has circular
wait: some process waits for itself through a chain of one or more wait-for edges.

The proof follows wait-for edges inside the deadlocked set; by finiteness it must revisit a
process.
