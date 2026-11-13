# Relaxation checks of Bellman-Ford pass by pass

For every list $E$ of weighted edges on
$n$ vertices and every source $s$, Bellman-Ford run on $E$ from $s$ charges exactly
$(n - 1) \cdot |E| + |E|$ relaxation checks, where $|E|$ is the length of $E$.

The two terms count one check per edge occurrence in each of the $n - 1$ ordinary passes and in
the final pass.
