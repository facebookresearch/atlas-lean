# Letting a process that fits finish preserves safety

Let $S$ be a system of processes
with maximum claims and current allocations, $w$ a vector of free resources (a natural number
for each resource type) and $L$ a list of pending processes without repetitions. If $p$ occurs in
$L$ and its remaining need $\mathrm{need}(p)$ in $S$ satisfies $\mathrm{need}(p) \le w$
componentwise, then $S$ is safe from $w$ for $L$ if and only if $S$ is safe from
$w + \mathrm{alloc}(p)$ for the list obtained from $L$ by removing $p$, where
$\mathrm{alloc}(p)$ is the current allocation of $p$ and the sum is taken componentwise.
