# The event of an LRU step

For a capacity $k$, a cache $c$ (a list of pages, most recently
used first) and a requested page $p$, the LRU event is a hit on $p$ if $p \in c$. Otherwise it is
a miss on $p$ that evicts the last page of $c$ (the least recently used one) if $c$ is nonempty,
$k > 0$ and $c$ has at least $k$ pages, and a miss on $p$ without eviction in all other cases.
