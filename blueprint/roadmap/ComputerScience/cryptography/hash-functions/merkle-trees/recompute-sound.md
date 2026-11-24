# Recomputation is sound up to collisions

Let $i$ be a position in a list of leaves. If recomputing for $k$ levels from $x$ at position $i$ with
some path gives $r$, and $r$ is node $\lfloor i/2^k \rfloor$ of the level $k$ steps up, then leaf $i$ is
$x$ or $h$ has a collision.
