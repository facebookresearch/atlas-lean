# The furthest-in-future manager produces legal traces

Let $k$ be a capacity, $R$ a list
of requested blocks and $C$ a duplicate-free list of blocks of length at most $k$. Let $E$ be the
events and $D$ the final cache produced by the furthest-in-future manager with capacity $k$ on
$R$ from the initial cache $C$. Then $E$ leads from $C$ to $D$ by legal cache transitions for
capacity $k$, the blocks requested by the events of $E$ are, in order, exactly $R$, and $D$ is
duplicate-free of length at most $k$.
