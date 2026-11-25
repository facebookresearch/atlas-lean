# Huffman trees beat every prefix-free code

Let Huffman's algorithm return the tree $t$ on a list $L$ of symbol–weight pairs with natural-number
weights. For every binary code $c$ that is prefix-free on the symbols of $L$, the weighted path length of
$t$ is at most the cost $\sum_{(a, w) \in L} w \, |c(a)|$. Codewords of symbols outside the input are
unconstrained, so this covers in particular every code that is prefix-free on the whole alphabet. No
codeword needs to be nonempty: for a one-symbol input the weighted path length is zero.
