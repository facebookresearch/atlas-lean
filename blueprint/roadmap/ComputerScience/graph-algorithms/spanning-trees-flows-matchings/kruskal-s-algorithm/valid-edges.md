# Valid edges of an input graph

For a graph $G$ on the vertices $\{0, \dots, n-1\}$ given
by its list of raw edges $e_0, e_1, \dots, e_{m-1}$, the valid edges of $G$ are, in input order,
the weighted edges obtained from those $e_k$ whose two endpoints are both less than $n$; each
keeps the endpoints and weight of $e_k$ and carries its zero-based input ordinal $k$. Edges with an
endpoint at least $n$ are omitted.
