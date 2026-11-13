# Valid edges in Kruskal order

For a finite weighted multigraph $G$ on the vertices
$\{0, \dots, n-1\}$, the ordered edges of $G$ are its valid input edges (those whose endpoints
are both less than $n$), sorted by merge sort in lexicographic order of (weight, input position):
by nondecreasing weight, with edges of equal weight in input order.
