# Huffman's encoded length beats every prefix-free code

Let Huffman's algorithm return the tree $t$ on a list $L$ of symbol–weight pairs with natural-number
weights. The encoded length of $t$ is its weighted path length, except that a tree consisting of a single
leaf of weight $w$ has encoded length $w$, because the encoder gives a lone symbol a one-bit codeword. For
every binary code $c$ that is prefix-free on the symbols of $L$ and gives each input symbol of positive
weight a nonempty codeword, the encoded length of $t$ is at most the cost
$\sum_{(a, w) \in L} w \, |c(a)|$. That hypothesis matters only for a one-symbol input of positive weight,
where the bound fails for the empty codeword: the encoded length charges the encoder's one-bit codeword,
while the empty codeword is prefix-free on one symbol and costs zero. A one-symbol input of weight zero
needs no nonempty codeword, since both sides are zero, and with two or more distinct input symbols
prefix-freeness already makes every input codeword nonempty. When the leaf symbols are distinct, the
encoded length is the encoder's emitted cost.
