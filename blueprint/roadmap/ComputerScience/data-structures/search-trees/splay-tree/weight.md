# Weight of a binary tree

For a real weight function $w$ on keys, the weight $W(t)$ of a binary tree $t$ is the sum, over
the nodes of $t$, of $w(k)$ for the key $k$ of the node; for $w = 1$ it is the number of nodes. With
positive weights, the weight of the subtree rooted at a node $x$ is Sleator and Tarjan's size
$s(x)$.

## Sources

- D. D. Sleator and R. E. Tarjan, *Self-adjusting binary search trees*, J. ACM 32(3) (1985)
  652–686, §2 (item weights and node sizes).
