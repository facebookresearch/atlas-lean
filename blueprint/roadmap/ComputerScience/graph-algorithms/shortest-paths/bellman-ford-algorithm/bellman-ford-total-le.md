# Bellman-Ford makes at most $4 n |E|$ counted steps

For every list $E$ of weighted edges
on $n$ vertices and every source $s$, the total cost of Bellman-Ford run on $E$ from $s$ (its
relaxation checks plus its negative-cycle witness reconstruction steps) is at most
$4 \cdot n \cdot |E|$, where $|E|$ is the length of $E$.
