# Circuits in an edge set

Let $\mathrm{end}_1, \mathrm{end}_2 : E \to V$ be maps, viewed
as an undirected multigraph on $V$ in which each edge $e \in E$ has endpoints $\mathrm{end}_1(e)$
and $\mathrm{end}_2(e)$. A finite set $F \subseteq E$ is a circuit when $F$ is nonempty, $F$ is
connected on its support, and every vertex in the support of $F$ has degree exactly $2$ in $F$,
where degree counts endpoint incidences, so that a loop contributes two.

This includes a loop as a $1$-circuit and two parallel edges between distinct vertices as a
$2$-circuit.
