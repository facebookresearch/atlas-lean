# Prim's algorithm returns a minimum spanning tree

Let $G$ be a connected simple graph on
the vertices $0, \dots, n-1$, let $D$ be a directed adjacency structure on the same vertices with
adjacency lists $A(u)$ such that for all vertices $u$ and $v$, $v$ occurs in $A(u)$ exactly when
$u$ and $v$ are adjacent in $G$, let $w$ assign a real weight $w(e)$ to every unordered pair $e$
of vertices, not necessarily distinct, and let $r$ be a vertex. Let $T$ be the simple graph on
the vertices $0, \dots, n-1$ in which two distinct vertices are adjacent when one of them is the
parent of the other in the output of Prim's algorithm on $D$, $w$ and $r$, and write $E(H)$ for
the edge set of a graph $H$. Then every edge of $T$ is an edge of $G$, $T$ is a tree, and every
graph $H$ on the vertices $0, \dots, n-1$ that is a tree and whose edges are all edges of $G$
satisfies $\sum_{e \in E(T)} w(e) \le \sum_{e \in E(H)} w(e)$.

Weights are arbitrary signed real numbers, and ties are allowed.
