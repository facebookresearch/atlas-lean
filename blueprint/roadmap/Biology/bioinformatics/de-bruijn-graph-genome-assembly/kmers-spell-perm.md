# Every Eulerian trail spells a string with the same k-mer multiset

Let $k \ge 2$, $s$ a string and $W = v_0, \dots, v_m$ a walk of words of length $k - 1$ whose steps $(v_i, v_{i+1})$ are a permutation of the edge occurrences of the [de Bruijn multigraph](de-bruijn-edges.md) of $s$ for $k$. Then the [$k$-mers](kmers.md) of the string [spelled](spell.md) by $W$ are a permutation of the $k$-mers of $s$. The empty walk is allowed; it is such a trail only when $s$ has no $k$-mers, and it spells the empty string.
