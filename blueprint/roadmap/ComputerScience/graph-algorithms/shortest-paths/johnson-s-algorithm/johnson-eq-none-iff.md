# Johnson's algorithm fails exactly on reachable negative cycles

For every list $E$ of
directed edges on the vertices $\{0, \dots, n-1\}$ with integer weights, Johnson's algorithm on
$E$ returns no table if and only if there is a vertex $s$ from which a negative cycle of $E$ is
reachable.
