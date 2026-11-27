# Admissible Huffman trees

Given an input list of symbols with natural-number weights, a
Huffman tree is admissible for the input when its list of weighted leaves, read from left to right,
is a permutation of the input list: the leaves of the tree carry exactly the input's (symbol,
weight) pairs, with the same multiplicities.

Every Huffman tree is a full binary tree, so admissibility imposes no further shape condition.
