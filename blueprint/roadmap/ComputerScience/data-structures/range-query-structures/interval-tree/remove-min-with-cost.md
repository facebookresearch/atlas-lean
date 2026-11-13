# Removing the leftmost entry, with its cost

Removing the leftmost entry of an interval
tree $T$ returns nothing when $T$ is empty. When the root's left subtree is empty, it returns the
root entry, the right subtree, and a cost of one node visit. Otherwise it removes the leftmost
entry $m$ of the left subtree recursively (returning nothing if that fails), rebuilds the root
node over the new left subtree with recomputed height, size and maximum high endpoint, and
rebalances that node; it returns $m$, the rebalanced tree, and the cost of the recursive call plus
one node visit and one cache write plus the cost of rebalancing.
