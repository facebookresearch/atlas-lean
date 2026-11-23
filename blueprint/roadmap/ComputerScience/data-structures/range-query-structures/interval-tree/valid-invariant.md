# Validity invariant of an interval tree

A tree satisfies the validity invariant when
every interval stored in it is valid, that is, its low endpoint is at most its high endpoint.
Recursively, the empty tree satisfies it, and a node satisfies it when its left subtree does,
the interval of its entry is valid, and its right subtree does.
