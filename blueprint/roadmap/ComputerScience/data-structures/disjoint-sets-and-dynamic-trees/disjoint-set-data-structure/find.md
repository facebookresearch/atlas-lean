# Root of a vertex in a parent forest

For a parent forest $F$ with parent map $p$ and a
vertex $x$, the root of $x$ is found by following parent pointers from $x$: it is $x$ itself
if $p(x) = x$, and otherwise it is the root of $p(x)$.
