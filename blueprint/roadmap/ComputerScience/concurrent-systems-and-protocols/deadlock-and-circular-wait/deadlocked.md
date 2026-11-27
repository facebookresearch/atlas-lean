# Deadlocked set of processes

In a resource-allocation snapshot $s$, a set $D$ of
processes is deadlocked when $D$ is nonempty and every process $p \in D$ waits in $s$ for some
process $q \in D$, that is, $p$ requests in $s$ a resource that $q$ holds in $s$.
