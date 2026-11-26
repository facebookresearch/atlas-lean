# A round of Luby's algorithm

Let $G$ be a graph on $\{0, \dots, n-1\}$ and let $\pi$
assign a priority in $\mathbb{N}$ to each vertex. A round takes a pair $(I, R)$ of the
independent set built so far and the set of remaining vertices to $(I \cup S, R')$, where $S$ is
the set of vertices of $R$ whose priority is smaller than that of every neighbor in $R$, ties
broken by vertex index (in particular every vertex of $R$ with no neighbor in $R$ is in $S$), and
$R'$ is the set of vertices of $R$ that are neither in $S$ nor adjacent to a vertex of $S$.
