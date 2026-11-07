# Leaf list of an internal node

For every internal node of a segment tree, with any cached
aggregate, any cached length, left child $L$ and right child $R$, its leaf list is the leaf list
of $L$ followed by the leaf list of $R$.

With the accumulator definition of the leaf list this is a theorem, not a definitional
unfolding.
