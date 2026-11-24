# Result of a treap split

For key type $\kappa$ and value type $\nu$, a split result
consists of a lower tree, an optional entry given by a value in $\nu$ together with a
natural-number priority, and an upper tree, where both trees are treap trees with keys in
$\kappa$ and values in $\nu$.

The structure imposes no constraint; on an ordered tree, splitting at a pivot fills the lower
tree with the keys below the pivot, the upper tree with the keys above it, and the entry with
the pivot's value and priority when the pivot occurs.
