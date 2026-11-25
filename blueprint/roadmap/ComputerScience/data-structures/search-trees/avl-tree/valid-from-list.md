# AVL trees built from a list are valid

Let $\alpha$ be a linearly ordered type. For every list $xs$ over $\alpha$, the tree obtained from the empty tree by AVL insertion of the entries of $xs$ one at a time, from the last entry to the first, is a valid AVL tree: it is ordered, has correct cached heights and is balanced.
