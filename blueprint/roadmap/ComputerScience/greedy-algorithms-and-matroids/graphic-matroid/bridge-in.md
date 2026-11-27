# Bridge test for an edge set

On a finite vertex set, for a finite set $S$ of unordered
pairs of vertices and a pair $e = \{u, v\}$, the bridge test returns true exactly when $u$ and $v$
are not connected by a path in the graph whose edges are the non-loop pairs of $S \setminus \{e\}$.
When $e \in S$ is not a loop, this says that $e$ is a bridge of $S$: deleting it disconnects its
endpoints.
