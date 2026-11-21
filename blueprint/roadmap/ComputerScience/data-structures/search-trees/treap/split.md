# Treap split

Let the keys come from a linear order, and write $(L, k, v, q, R)$ for the
node with left subtree $L$, key $k$, value $v$, priority $q$ and right subtree $R$. Splitting
a tree at a pivot $p$ returns a split result, defined by recursion on the tree. The empty tree
splits into two empty trees and no entry. For a node $(L, k, v, q, R)$: if $k < p$, split $R$
at $p$ into a lower tree $R_1$, an optional entry $e$ and an upper tree $R_2$, and return the
lower tree $(L, k, v, q, R_1)$, the entry $e$ and the upper tree $R_2$; if $p < k$, split $L$
at $p$ into $L_1$, $e$ and $L_2$, and return the lower tree $L_1$, the entry $e$ and the upper
tree $(L_2, k, v, q, R)$; otherwise $k = p$, and return the lower tree $L$, the entry
$(v, q)$ and the upper tree $R$.

On an ordered tree, the lower tree holds the keys below $p$, the upper tree holds the keys
above $p$, and the entry is the value and priority stored at $p$ when $p$ occurs.
