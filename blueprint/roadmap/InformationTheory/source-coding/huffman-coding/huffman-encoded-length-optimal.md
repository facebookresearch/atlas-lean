# Huffman's algorithm minimizes the encoded length

Let $L$ be a list of symbol–weight
pairs with natural-number weights, over a symbol type with decidable equality, and suppose
Huffman's algorithm returns the tree $t$ on $L$. Then every Huffman tree $t'$ that is admissible
for $L$, that is, whose weighted leaves listed from left to right form a permutation of $L$, has
encoded length at least that of $t$.

The encoded length charges a lone leaf for a one-bit codeword; when the leaf symbols of a tree
are distinct, it equals the encoder's emitted cost, the total weighted codeword length.
