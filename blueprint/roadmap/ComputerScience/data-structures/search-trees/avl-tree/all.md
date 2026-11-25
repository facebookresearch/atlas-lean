# Every key of an AVL tree satisfies a predicate

For a predicate $p$ on keys and a tree $t$
with cached heights, $\mathrm{All}(p, t)$ holds when $p$ holds at the key of every node of $t$. It
is defined as the corresponding predicate on the plain binary tree obtained from $t$ by erasing
its cached heights.
