# Suffix sums

Let $n$ nodes be linked into lists by a partial successor function, each
node $v$ carrying a value $x_v$ in an additive monoid $M$. The suffix sum of a node $v$ is the
segment sum of length $n$ from $v$: the sum, in list order, of the values of the first $n$ nodes
of the list starting at $v$ (fewer if it ends sooner).

When the list from $v$ ends, it has at most $n$ nodes, so this is the sum of the values from $v$
to the end of its list.
