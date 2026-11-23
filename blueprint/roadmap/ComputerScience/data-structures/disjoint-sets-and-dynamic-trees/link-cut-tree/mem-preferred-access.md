# Access keeps off-path preferred edges

Let $s$ be a link-cut tree state, $x$ a vertex,
and $(u, w)$ a preferred edge of $s$, directed from the parent $u$ to the child $w$. Suppose
that, if some tree of the represented forest of $s$ contains $x$, then $u$ does not lie on the
path in the first such tree from its root down to the first occurrence of $x$ in preorder. Then
$(u, w)$ is still a preferred edge after accessing $x$.

This is the edge-level fact behind the persistence of off-path preferred paths across
accesses.
