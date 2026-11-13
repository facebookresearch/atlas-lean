# Insertion into a 2-3 tree root

To insert a key $x$ into a root, that is, a 2-3 tree
together with its height $h$, insert $x$ into the underlying tree. If this returns a single tree
of height $h$, that tree is the new root, of height $h$. If it returns a split into trees $l$
and $r$ around a key $k$, the new root is the 2-node with key $k$ and children $l$ and $r$, of
height $h + 1$.
