# Splaying preserves the weight of a tree

For every weight function $w$, key $x$ and binary tree $t$, the [splayed tree](splay.md) $S_x(t)$
has the same [weight](weight.md) as $t$: $W(S_x(t)) = W(t)$. Splaying preserves the inorder
sequence of keys, and the weight is the sum of $w$ over that sequence. In the amortized analysis
this keeps the total weight $W$ fixed along a sequence of splays.
