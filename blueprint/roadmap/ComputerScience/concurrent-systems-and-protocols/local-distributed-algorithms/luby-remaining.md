# Vertices left after a round of Luby's algorithm

Let $G$ be a graph on
$\{0, \dots, n-1\}$, let $\pi$ assign a priority in $\mathbb{N}$ to each vertex and let $R$ be the
set of remaining vertices. The vertices left after the round are those of $R$ that are neither
selected by the selection step of Luby's algorithm (the vertices of $R$ whose priority is smaller
than that of every neighbor in $R$, ties broken by vertex index) nor adjacent to a selected
vertex.
