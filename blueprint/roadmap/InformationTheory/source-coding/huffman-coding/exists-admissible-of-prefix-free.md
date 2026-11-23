# From prefix-free codes to admissible trees

For a nonempty list $L$ of symbol–weight pairs with distinct symbols and natural-number weights, and a
binary code $c$ that is prefix-free on the symbols of $L$, some admissible tree, a full binary tree whose
weighted leaves are a permutation of $L$, has weighted path length at most the code's cost
$\sum_{(a, w) \in L} w \, |c(a)|$. The tree returned by Huffman's algorithm is one. Codewords of symbols
outside the input are unconstrained, and no codeword needs to be nonempty.
