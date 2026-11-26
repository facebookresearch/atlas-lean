# Keyed erasure with cost

Erasing a key $k \in \mathbb{Z} \times \mathbb{N}$ from an
interval tree returns a new tree together with its cost; the key of an entry is the pair of its low
endpoint and identifier, and keys are compared lexicographically. The empty tree is returned
unchanged at a cost of one node visit. At a node with entry $x$, the key $k$ is compared with the
key of $x$. If $k$ is smaller, $k$ is erased from the left subtree; if it is larger, from the right
subtree; in both cases the node is rebuilt with the new subtree and rebalanced, and the cost is the
subtree's cost plus one node visit, one key comparison, one cache write and the rebalancing cost.
If $k$ equals the key of $x$ and the right subtree is empty (so it has no leftmost entry to
remove), the result is the left subtree at a cost of one node visit and one key comparison.
Otherwise the leftmost entry of the right subtree is removed and takes the place of $x$, the node
is rebuilt and rebalanced, and the cost is the removal's cost plus one node visit, one key
comparison, one cache write and the rebalancing cost.
