# Degree within an edge set

Let $\mathrm{end}_1, \mathrm{end}_2 : E \to V$ be maps, viewed
as an undirected multigraph on $V$ in which each edge $e \in E$ has endpoints $\mathrm{end}_1(e)$
and $\mathrm{end}_2(e)$. For a finite set $F \subseteq E$ and a vertex $v \in V$, the degree of
$v$ in $F$ is the number of $e \in F$ with $\mathrm{end}_1(e) = v$ plus the number of $e \in F$
with $\mathrm{end}_2(e) = v$. Each endpoint incidence counts once, so a loop at $v$ contributes
two.
