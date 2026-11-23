# Valid range tree

A range tree $t$ is valid when it has correct cached bounds (every node
has two subtrees with nonempty leaf lists, and its stored lower and upper bounds are the minimum
of the lower bounds and the maximum of the upper bounds of its two subtrees, recursively) and
its leaf list is sorted in nondecreasing order.
