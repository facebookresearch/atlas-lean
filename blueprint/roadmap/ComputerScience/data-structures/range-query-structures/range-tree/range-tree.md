# Range tree

A one-dimensional range tree over the integers is either empty, a single leaf
holding an integer, or a binary node made of two integers $l$ and $h$ together with a left and a
right subtree. The integers $l$ and $h$ are meant to cache the interval $[l, h]$ spanned by the
leaf values of the node's subtree; the type does not enforce this, the bounds-correctness
predicate does.
