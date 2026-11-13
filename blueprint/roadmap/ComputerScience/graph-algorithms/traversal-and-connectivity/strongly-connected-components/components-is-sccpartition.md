# The computed components form the SCC partition

For every directed graph $G$, the list of
blocks returned by the strongly connected components algorithm on $G$ is an SCC partition of $G$:
every block is nonempty and contains no vertex twice, blocks at different positions of the list
are disjoint, every vertex of $G$ lies in some block, two vertices lie in a common block exactly
when they are strongly connected, and for every vertex $m$ of a block $B$ and every vertex $v$,
the vertices $m$ and $v$ are strongly connected exactly when $v$ lies in $B$.
