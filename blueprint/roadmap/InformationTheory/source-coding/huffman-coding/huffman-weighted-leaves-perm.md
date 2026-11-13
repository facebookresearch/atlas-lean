# Huffman's construction keeps the weighted leaves

Let $L$ be a list of pairs $(a, w)$ of
a symbol $a$ and a natural-number weight $w$, with decidable equality on symbols. If the Huffman
construction on $L$ succeeds with a tree $T$, then the list of weighted leaves of $T$, read left
to right, is a permutation of $L$.
