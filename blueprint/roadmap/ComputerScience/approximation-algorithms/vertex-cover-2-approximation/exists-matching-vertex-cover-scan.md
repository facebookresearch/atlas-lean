# Matching invariant of the vertex cover scan

Let $G$ be a simple graph, $C_0$ a finite set
of vertices, and $L$ a list of ordered pairs of vertices such that $u$ and $v$ are adjacent in $G$
for every $(u, v)$ in $L$, and let $C$ be the cover that the vertex cover scan returns on $L$
starting from $C_0$. Then there is a sublist $A$ of $L$ such that neither endpoint of any pair in
$A$ lies in $C_0$, pairs at different positions of $A$ are vertex-disjoint, a vertex lies in $C$
exactly when it lies in $C_0$ or is an endpoint of some pair in $A$, and $|C| = |C_0| + 2|A|$,
where $|A|$ is the length of $A$.
