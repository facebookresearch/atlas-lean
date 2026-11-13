# Optimality of Huffman coding

Let $L$ be a list of symbol–weight pairs with
natural-number weights, over a symbol type with decidable equality, and suppose the Huffman
construction returns the tree $t$ on $L$. Then every coding tree $t'$ (a full binary tree whose
leaves carry symbols and weights) whose weighted leaves, listed left to right, form a permutation
of $L$ has weighted path length at least that of $t$.
