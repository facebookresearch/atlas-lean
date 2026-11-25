# Top-down B-tree deletion

Deleting a key $x$ of a linearly ordered key type from a tree $T$
with minimum degree $t$ applies height-indexed deletion of $x$ with minimum degree $t$ to $T$ at
the height of $T$, where the height of a leaf, or of an internal node without children, is $0$,
and the height of any other internal node is one more than the height of its first child. If the
outcome is an internal node with no keys and exactly one child, the result is that child;
otherwise the result is the outcome itself.

This is the top-down deletion of CLRS Section 18.3: the tree is repaired on the way down from the
root.

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*, 3rd ed.,
  MIT Press, 2009, Section 18.3 (top-down deletion).
