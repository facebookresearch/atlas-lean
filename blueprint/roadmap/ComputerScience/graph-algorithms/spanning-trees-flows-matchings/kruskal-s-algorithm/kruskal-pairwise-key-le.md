# Kruskal's output is sorted by key

For every graph $G$, if an edge $e$ comes before an
edge $f$ in the list returned by Kruskal's algorithm on $G$, then $e$ has smaller weight than
$f$, or the same weight as $f$ and input ordinal at most that of $f$.
