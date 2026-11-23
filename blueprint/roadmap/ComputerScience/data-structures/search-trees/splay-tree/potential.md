# Splay-tree potential

For a binary tree $t$, write $|u|$ for the number of nodes of a subtree $u$. The potential of $t$
is

$$\Phi(t) = \sum_{x \in t} \log_2 |t_x|,$$

the sum over the nodes $x$ of $t$ of the rank $\log_2 |t_x|$ of the subtree $t_x$ rooted at
$x$. This is Sleator and Tarjan's potential with every item of weight one, so that the size
$s(x)$ of a node is the number of nodes below it.

## Sources

- D. D. Sleator and R. E. Tarjan, *Self-adjusting binary search trees*, J. ACM 32(3) (1985)
  652–686, §2 (sizes, ranks and potential; binary logarithms throughout).
