# Witness cost of a returned negative cycle

For every list $E$ of weighted edges on $n$
vertices and every source $s$, if Bellman-Ford run on $E$ from $s$ returns a reachable negative
cycle whose cycle has $c$ edges and whose path from $s$ to the cycle has $q$ edges, then the run
charges exactly $n + c + q$ negative-cycle witness reconstruction steps.
