# Adjacency through an edge set

Let $\mathrm{end}_1, \mathrm{end}_2 : E \to V$ be maps,
viewed as an undirected multigraph on $V$ in which each edge $e \in E$ has endpoints
$\mathrm{end}_1(e)$ and $\mathrm{end}_2(e)$. For a finite set $F \subseteq E$, vertices
$u, v \in V$ are adjacent using $F$ when some $e \in F$ has $\mathrm{end}_1(e) = u$ and
$\mathrm{end}_2(e) = v$, or $\mathrm{end}_1(e) = v$ and $\mathrm{end}_2(e) = u$.
