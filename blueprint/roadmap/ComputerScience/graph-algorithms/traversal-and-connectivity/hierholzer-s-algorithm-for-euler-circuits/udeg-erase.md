# Degree after removing an edge

Let $R$ be a finite list of edges of an undirected
multigraph, each an ordered pair of vertices, let $e = (a, b)$ be an edge in $R$, and let $x$ be a
vertex. Then the degree of $x$ in $R$ equals the degree of $x$ in the list obtained from $R$ by
removing the first occurrence of $e$, plus $[x = a] + [x = b]$, where $[P]$ is $1$ if $P$ holds
and $0$ otherwise.
