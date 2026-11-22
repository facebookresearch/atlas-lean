# Counting invariant of the vertex cover scan

Let $G$ be a simple graph, $S$ a vertex cover
of $G$, $C_0$ a finite set of vertices with $|C_0| \le 2|C_0 \cap S|$, and $L$ a list of ordered
pairs of vertices such that $u$ and $v$ are adjacent in $G$ for every $(u, v)$ in $L$. Then the
cover $C$ that the vertex cover scan returns on $L$ starting from $C_0$ satisfies
$|C| \le 2|C \cap S|$.

The invariant holds because each taken edge adds two new vertices, at least one of them in $S$.
