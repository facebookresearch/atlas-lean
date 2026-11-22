# Splitting a node's flattening at a separator

Let $K_1$ and $K_2$ be lists of keys, $m$ a
key, and $C_1$ and $C_2$ lists of raw B-trees such that $C_1$ has exactly one more element than
$K_1$. Then the flattening of the node whose key list is $K_1$ followed by $m$ followed by $K_2$
and whose child list is $C_1$ followed by $C_2$ equals the flattening of the node with keys $K_1$
and children $C_1$, followed by $m$, followed by the flattening of the node with keys $K_2$ and
children $C_2$.
