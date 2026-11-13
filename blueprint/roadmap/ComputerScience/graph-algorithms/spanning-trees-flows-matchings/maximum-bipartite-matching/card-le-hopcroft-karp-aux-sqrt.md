# Hopcroft and Karp's bound on the number of phases

In a bipartite graph with $b$ right
vertices, run at most $2 \lfloor \sqrt{b} \rfloor + 2$ Hopcroft–Karp phases from the empty
matching, stopping early when a phase finds no augmenting path. Then no matching of the graph has
more edges than the resulting one.

After the first $\lfloor \sqrt{b} \rfloor + 1$ phases every augmenting path has more than
$\lfloor \sqrt{b} \rfloor$ pairs, so the deficit against any matching is at most
$\lfloor \sqrt{b} \rfloor$, and each further phase adds an edge.
