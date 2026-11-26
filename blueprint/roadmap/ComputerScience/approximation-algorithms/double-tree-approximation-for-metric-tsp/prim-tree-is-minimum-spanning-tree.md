# Prim's tree is a minimum spanning tree

Let $d(u,v)$ be real costs on the vertices
$\{0, \dots, n-1\}$, let $r$ be a vertex, and weigh each edge $\{u, v\}$ by $d(u,v) + d(v,u)$.
Then Prim's tree for $d$ and $r$ is a tree, and for every tree $H$ on these vertices the total
weight of the edges of Prim's tree is at most the total weight of the edges of $H$.
