# Treap all-nodes predicate via node membership

Let $p$ be a predicate on a key, a value
and a natural-number priority, and let $t$ be a tree. Then $p$ holds at every node of $t$ if and
only if $p(k, v, n)$ holds for every key $k$, value $v$ and priority $n$ such that the entry
$(k, v, n)$ occurs as a node of $t$.
