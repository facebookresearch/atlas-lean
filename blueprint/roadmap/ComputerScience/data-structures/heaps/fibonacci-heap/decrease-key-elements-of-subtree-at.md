# Decrease-key replaces one key, stated by address

Let $H$ be a Fibonacci heap, let $T$ be
the $i$-th tree of its root list, and let $S$ be the subtree of $T$ at the path $p$ of child
indices. If the key $k$ is at most the root of $S$, then the multiset represented by the heap
obtained from $H$ by decreasing the key at root index $i$ and path $p$ to $k$ is the multiset
represented by $H$ with one occurrence of the root of $S$ removed and one occurrence of $k$
added.
