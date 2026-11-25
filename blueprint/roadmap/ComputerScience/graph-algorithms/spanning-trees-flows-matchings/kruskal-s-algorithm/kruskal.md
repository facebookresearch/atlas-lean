# Kruskal's algorithm

For a finite weighted multigraph $G$ on the vertices
$\{0, \dots, n-1\}$, Kruskal's algorithm starts from the partition of the vertices into
singletons and processes the valid input edges of $G$ (those whose endpoints are both less than
$n$) in lexicographic order of (weight, input position). An edge whose endpoints lie in different
classes of the current partition is accepted and its two classes are merged; an edge whose
endpoints lie in the same class is skipped. The result is the list of accepted edges in the order
in which they were processed.
