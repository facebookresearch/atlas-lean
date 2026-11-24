# An edge cut keeps every other edge

Let $s$ be a valid link-cut tree state and let $x$ and
$y$ be adjacent in some tree of its represented forest. If $a$ and $b$ are adjacent in some tree
of the represented forest of $s$, and neither $a = x$ and $b = y$ nor $a = y$ and $b = x$, then
$a$ and $b$ are adjacent in some tree of the represented forest obtained from $s$ by cutting the
edge between $x$ and $y$.

Edges of other trees pass through untouched; edges of the cut tree survive the rerooting at $x$
and then lie on one side of the prune at $y$, and the only edge crossing the prune is the edge
between $x$ and $y$.
