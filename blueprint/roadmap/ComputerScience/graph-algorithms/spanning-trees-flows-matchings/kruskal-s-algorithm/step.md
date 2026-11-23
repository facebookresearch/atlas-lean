# One Kruskal step

Let $s$ be a Kruskal scan state and $e$ a validated edge with endpoints
$u$ and $v$. If $u$ and $v$ are equivalent in the union-find forest of $s$, processing $e$ leaves
$s$ unchanged. Otherwise $e$ is accepted: the new forest is the union of $u$ and $v$ in the forest
of $s$, and $e$ is put at the front of the list of accepted edges.
