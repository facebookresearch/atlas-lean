# B-tree insertion

For minimum degree $t$, the tree obtained by inserting a key $x$ into a
tree $T$ is computed from the split-returning insertion of $x$ into $T$: if that returns a single
tree, this tree is the result; if it returns two trees $\ell$ and $r$ with a promoted median key
$m$, the result is a new root node with the single separator $m$ and the two children $\ell$ and
$r$.

When $T$ is a B-tree of minimum degree $t$, inserting a key already present in $T$ returns a tree
with the same flattening.
