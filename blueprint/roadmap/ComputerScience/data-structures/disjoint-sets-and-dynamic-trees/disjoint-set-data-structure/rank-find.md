# Path compression preserves ranks

Let $S$ be a union-find structure and $x$ a node of
$S$, and let $S'$ be the structure returned by FIND on $x$ with path compression. For every
natural number $i$, the rank of $i$ in $S'$ equals the rank of $i$ in $S$, where the rank of an
index that is not a node is $0$.
