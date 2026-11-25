# Undirected Hierholzer's algorithm finds Euler circuits

Let $E$ be a list of undirected
edges (ordered pairs of vertices) in which every vertex has even degree, and let $s$ be a vertex
such that the first endpoint of every edge of $E$ is reachable from $s$ through edges of $E$. Then
the vertex sequence returned by the undirected Hierholzer algorithm on $E$ from $s$ is an Euler
path of $E$ from $s$ to $s$, that is, an Euler circuit at $s$.
