# The key of a vertex in Luby's algorithm

For a graph on the vertices $0, \dots, n-1$ with priorities $p(v) \in \mathbb{N}$, the key of a vertex $v$ is the natural number $p(v) \cdot n + v$. Comparing keys compares priorities first and breaks ties between equal priorities by vertex index.
