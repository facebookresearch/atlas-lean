# Accumulator traversal of a segment tree

Given a segment tree and a list $acc$, the
accumulator traversal returns $acc$ for the empty tree, the list $acc$ with $x$ prepended for a
leaf with value $x$, and, for an internal node with left child $L$ and right child $R$, the
traversal of $L$ starting from the result of the traversal of $R$ starting from $acc$.

Threading the output suffix this way collects the leaves of an $n$-leaf tree in linear time
instead of repeatedly appending (and copying) left-subtree results.
