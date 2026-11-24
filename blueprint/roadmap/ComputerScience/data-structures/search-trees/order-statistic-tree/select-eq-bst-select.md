# Cached select agrees with inorder select

For every order-statistic tree $T$ whose
cached subtree sizes are correct and every natural number $i$, select at index $i$ in $T$
(descending with the cached sizes) returns the same result as taking the element at zero-based
position $i$ of the inorder traversal of the binary tree obtained from $T$ by erasing the cached
sizes; in particular both return nothing when that position does not exist.
