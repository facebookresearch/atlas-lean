# Undirected Hierholzer recursion

The recursion takes a fuel $f \in \mathbb{N}$, a vertex
$v$, a list $R$ of remaining edges and an accumulator list $A$ of vertices, and returns a list of
vertices and a list of remaining edges. With fuel $0$ it returns $A$ and $R$ unchanged. With fuel
$f + 1$: if no edge of $R$ has $v$ as an endpoint, it returns $v$ prepended to $A$, together with
$R$; otherwise, with $e$ the first such edge, it removes $e$ from $R$ at a cost of one unit,
recurses with fuel $f$ from the other endpoint of $e$ at $v$ on the shortened list with
accumulator $A$, obtaining a vertex list $A'$ and remaining edges $R'$, and then recurses with fuel
$f$ from $v$ on $R'$ with accumulator $A'$.
