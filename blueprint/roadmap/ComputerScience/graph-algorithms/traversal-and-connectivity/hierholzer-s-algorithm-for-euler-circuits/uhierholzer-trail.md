# Undirected Hierholzer's algorithm returns a trail

Let $E$ be a list of undirected edges
and $s$, $t$ vertices such that exactly $s$ and $t$ have odd degree in $E$ (no vertex has odd
degree when $s = t$). Then the vertex sequence $W$ returned by the undirected Hierholzer algorithm
on $E$ from $s$ starts at $s$ and ends at $t$, and the consecutive pairs of $W$, as unordered
pairs, form a sub-multiset of the edges of $E$ as unordered pairs: no edge is traversed more often
than it occurs in $E$.
