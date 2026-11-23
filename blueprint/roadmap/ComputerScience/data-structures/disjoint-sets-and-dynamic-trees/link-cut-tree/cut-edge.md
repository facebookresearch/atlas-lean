# Cutting an edge of a link-cut tree

For vertices $x$ and $y$ and a link-cut tree state
$s$, cutting the edge between $x$ and $y$ works as follows. If $x$ and $y$ are adjacent in some
tree of the represented forest of $s$, the result is obtained from $s$ by first making $x$ the
root of its represented tree and then cutting off the subtree rooted at $y$. Otherwise the
represented forest is left unchanged. In both cases the list of preferred edges becomes empty.

When $x$ and $y$ are joined by an edge of a valid state, making $x$ the root turns $y$ into the
root of a child subtree of $x$, so the cut separates the two sides of the edge between $x$ and
$y$ and keeps every other edge.

The adjacency test is necessary: without it the composite would cut at $y$ regardless of $x$.
For instance, on the chain $1 \to 2$ it would detach $2$ when asked to cut the edge between
$99$ and $2$, although there is no such edge.
