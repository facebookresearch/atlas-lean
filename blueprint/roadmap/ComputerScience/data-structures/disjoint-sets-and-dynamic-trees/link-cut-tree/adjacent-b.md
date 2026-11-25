# Adjacency test

For vertices $a$, $b$ and a rooted tree $t$ with root $r$ and child
subtrees $c_1, \dots, c_k$, the adjacency test of $a$ and $b$ in $t$ returns true exactly when
$r = a$ and some $c_i$ has root $b$, or $r = b$ and some $c_i$ has root $a$, or the adjacency test
of $a$ and $b$ returns true in some $c_i$.

It returns true exactly when $a$ and $b$ are adjacent in $t$, and it is the guard checked by the
edge cut before it cuts.
