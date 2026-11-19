# Keyed insertion with cost

Inserting an entry $x$ into a tree returns a new tree together
with an operation cost; keys (low endpoint, then identifier) are compared lexicographically. Into
the empty tree, $x$ is inserted as a single node, at a cost of one node visit and one cache write.
At a node with entry $y$: if the key of $x$ equals the key of $y$, then $y$ is replaced by $x$, at a
cost of one node visit, one key comparison and one cache write; if the key of $x$ is smaller
(respectively larger), then $x$ is inserted recursively into the left (respectively right)
subtree, the node is rebuilt with recomputed metadata and rebalanced, and the cost is the cost of
the recursive insertion, plus one node visit, one key comparison and one cache write, plus the
cost of rebalancing.
