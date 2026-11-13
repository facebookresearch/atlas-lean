# Huffman's construction fails exactly on empty or repeated-symbol inputs

Let $L$ be a
list of symbol–weight pairs with natural-number weights, over a symbol type with decidable
equality. The Huffman construction returns no tree on $L$ if and only if $L$ is empty or some
symbol occurs in $L$ more than once.
