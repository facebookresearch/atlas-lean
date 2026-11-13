# Granting a request

For a system $S$ of processes with maximum claims and current
allocations, a process $p$ and a resource vector $r$ (a natural number for each resource type),
the system obtained by granting $r$ to $p$ has the same maximum claims as $S$, gives $p$ the
allocation $\mathrm{alloc}(p) + r$ (componentwise sum, where $\mathrm{alloc}(p)$ is the current
allocation of $p$ in $S$), and leaves the allocation of every other process unchanged.
