# Granted requests lead to safe states

Let $S$ be a system of processes with maximum
claims and current allocations, $a$ the vector of free resources, $L$ the list of pending
processes, $p$ a process and $r$ a resource vector. If the resource-request algorithm grants the
request of $r$ by $p$, returning the free vector $a'$ and the system $S'$, then $S'$ is safe from
$a'$ for $L$.
