# Remaining need

The remaining need of a process $p$ in a system $S$ is the resource
vector $\mathrm{claim}(p) - \mathrm{alloc}(p)$: the maximum claim of $p$ minus its current
allocation, computed for each resource type by truncated subtraction of natural numbers, so it
is $0$ for every resource type where the allocation exceeds the claim.
