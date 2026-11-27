# Search in an ordered red-black tree is correct

Let $t$ be a red-black tree over a
linearly ordered type that is ordered (every left key is smaller and every right key larger,
recursively). Then for every key $x$, the search for $x$ in $t$ returns true if and only if $x$
is a key of some node of $t$.
