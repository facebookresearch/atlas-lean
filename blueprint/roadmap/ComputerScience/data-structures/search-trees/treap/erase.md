# Treap deletion

For a key $k$ of a linearly ordered key type and a tree $t$, deleting
$k$ from $t$ splits $t$ at $k$ and returns the priority-guided merge of the part of the split
below $k$ with the part above $k$; the entry the split finds at $k$, if any, is dropped.
