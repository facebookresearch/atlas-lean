# Vertex list of an indexed walk

The support of an indexed walk $p$ from $u$ to $v$ in
an edge-indexed multigraph is the list of the vertices that $p$ visits, in order and with
repetitions, including both endpoints: the empty walk at $w$ has support $[w]$, and a walk that
starts at $u$ with an edge and continues with an indexed walk $q$ has support $u$ followed by
the support of $q$.
