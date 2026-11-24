# Parent chains in a DFS forest end at a forest root

Let $G$ be a finite directed graph and
$R$ a list of root vertices, and run depth-first search on $G$ from $R$. Say that $p$ is a recorded
parent of $c$ when the pair $(c, p)$ occurs in the list of (child, parent) pairs recorded by the
search, and call a discovered vertex with no recorded parent a forest root. Then for every
vertex $v$ in the discovery order (preorder) there are $k \ge 0$ and vertices
$v = v_0, v_1, \dots, v_k$ such that each $v_{i+1}$ is a recorded parent of $v_i$ and $v_k$ is a
forest root.
