# Codeword of a leaf symbol

For a Huffman tree $T$ and a symbol $s$ occurring at a
leaf of $T$, the codeword of $s$ is the word that the codeword lookup of $T$ returns for $s$,
or the empty word if the lookup fails.

The lookup never fails on a leaf symbol, so the empty-word default is never used.
