# One round of the layered search bounds the deficit

Let a bipartite graph have left vertices $\{0, \dots, a - 1\}$, right vertices
$\{0, \dots, b - 1\}$ and adjacency lists, and let a current matching be given by assigning to
each right vertex at most one partner, a neighbour, with no left vertex the partner of two right
vertices. For $k \in \mathbb{N}$ let $Z_k$ and $R_k$ be the left and right vertices reached within
$k$ rounds of the alternating breadth-first search: $Z_0$ is the set of unmatched left vertices
and $R_0 = \emptyset$; $R_{k+1}$ is the set of right vertices $j$ adjacent to some $i \in Z_k$ of
which $j$ is not the partner; and $Z_{k+1}$ consists of $Z_k$ together with the partners of the
vertices of $R_{k+1}$.

Let $k \in \mathbb{N}$ be such that no unmatched right vertex lies in $R_{k+1}$. Then every matching
$M$ of the graph satisfies

$$|M| \le |C| + |R_{k+1} \setminus R_k|,$$

where $C$ is the current matching. Indeed the left vertices outside $Z_k$ together with $R_{k+1}$
cover every edge.
