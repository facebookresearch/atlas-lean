# Cut in the Aho graph

For a finite set $R$ of [triplets](triplet.md) and a finite set $S'$ of taxa, the Aho graph of $R$ on $S'$ has a cut if there is $K \subseteq S'$ with $K$ and $S' \setminus K$ nonempty such that for every $xy \mid z \in R$ with $x, y, z \in S'$, $x \in K$ if and only if $y \in K$: the graph on $S'$ with an edge $xy$ for each such triplet is disconnected.
