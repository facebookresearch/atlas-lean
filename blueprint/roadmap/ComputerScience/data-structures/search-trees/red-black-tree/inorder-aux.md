# Inorder traversal onto a suffix

For a red-black tree $t$ and a list $s$, this is the
accumulator form of the binary-search-tree inorder traversal applied to the color erasure of $t$:
for the empty tree it returns $s$, and for a node with key $k$ and subtrees $l$ and $r$ it returns
the result for $l$ with suffix the list $k$ followed by $u$, where $u$ is the result for $r$ with
suffix $s$.

Thus the result lists the keys of $t$ in inorder followed by $s$, in time linear in the size
of $t$.
