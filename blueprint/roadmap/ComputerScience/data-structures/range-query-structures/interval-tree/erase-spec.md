# Correctness of erasure from the indexed interval tree

Let $T$ be an indexed interval tree
satisfying the representation invariant, and let $i$ be a natural number. Then the tree obtained by
erasing identifier $i$ from $T$ again satisfies the invariant, and an entry is stored in it if and
only if it is stored in $T$ and its identifier differs from $i$.

In particular, if no stored entry has identifier $i$, the stored entries are unchanged.
