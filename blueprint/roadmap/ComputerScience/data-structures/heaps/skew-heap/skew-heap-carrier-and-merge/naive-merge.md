# Naive Merge

The "tempting" merge function from §14.1: same as `merge` but
without swapping the children. Functionally correct (Exercise 14.2),
but it can produce very unbalanced heaps — the motivation for skew
heaps, which swap on every node of the merge path.
