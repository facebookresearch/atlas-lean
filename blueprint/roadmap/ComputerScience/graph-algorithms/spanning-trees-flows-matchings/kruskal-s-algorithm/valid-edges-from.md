# Validating an edge list from a given ordinal

Given $n$, a starting ordinal $o$ and a
list of raw edges $e_0, e_1, \dots, e_{m-1}$, this returns, in input order, the weighted edges on
the vertices $\{0, \dots, n-1\}$ obtained from those $e_k$ whose two endpoints are both less than
$n$; each keeps the endpoints and weight of $e_k$ and carries the ordinal $o + k$. Edges with an
endpoint at least $n$ are omitted, but they still count towards the ordinals of later edges.
