# Turning an insertion result into a 2-3 tree

An insertion result at height $h$ becomes a
2-3 tree of unspecified height as follows: a tree $t$ of height $h$ gives $t$ itself, of height
$h$, and a split into trees $l$, $r$ of height $h$ around a key $k$ gives the 2-node with
separator $k$, left child $l$ and right child $r$, of height $h + 1$.
