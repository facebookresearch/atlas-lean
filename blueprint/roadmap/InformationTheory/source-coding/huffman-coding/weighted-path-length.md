# Weighted path length

The weighted path length of a Huffman tree is defined recursively:
a single leaf has weighted path length $0$, and the tree with left subtree $L$ and right subtree
$R$ has weighted path length equal to the weighted path length of $L$ plus that of $R$ plus the
total weight of $L$ plus the total weight of $R$.

Equivalently, it is the sum over the leaves of each leaf's weight times its depth, with the root
at depth zero (the standard weighted external path length).
