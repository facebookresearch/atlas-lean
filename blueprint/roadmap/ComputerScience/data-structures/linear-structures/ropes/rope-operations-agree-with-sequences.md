# Rope operations agree with the sequence model

For a rope $t$ representing the sequence $L$: the cached length of $t$ equals $|L|$ and its cached height equals its structural height; indexing $t$ at position $i$ returns $L_i$ (or nothing if $i \ge |L|$) by descending with the cached lengths, in time proportional to the height; mapping a function over the leaves represents the mapped sequence and preserves well-formedness; left and right folds over $t$ equal the folds over $L$. Bulk construction from a list $L$ with $B \ge 1$ produces a rope with correct caches representing $L$ whose leaves hold between $1$ and $B$ elements, and the children of a well-formed node are well formed.

## Proof sketch

Each claim follows by structural induction on the rope, using that the represented sequence of a node is the concatenation of its children's sequences and that a node's cached length splits indices between the left and right child.

## Depends on

- [Rope](rope.md)

## Sources

- H.-J. Boehm, R. Atkinson and M. Plass, "Ropes: an Alternative to Strings", Software: Practice and Experience 25(12), 1995.
