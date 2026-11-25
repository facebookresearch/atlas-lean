# From an indexed walk to a walk in the underlying graph

Let $M$ be an edge-indexed
multigraph. An indexed walk $p$ in $M$ from $u$ to $v$ yields a walk from $u$ to $v$ in the
underlying simple graph of $M$ by forgetting edge identities: the empty indexed walk at $w$ goes
to the empty walk at $w$, and an indexed walk that first traverses an edge $e$ with endpoints
$\{u, x\}$ and then continues with an indexed walk $q$ goes to the walk that first steps from $u$
to $x$, an edge of the underlying graph because $e$ has these endpoints, and then follows the
image of $q$.
