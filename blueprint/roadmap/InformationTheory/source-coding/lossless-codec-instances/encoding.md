# Huffman codec

For a Huffman tree $T$, the codec on messages over the symbols that label leaves of $T$, with alphabet the bits: a message is encoded by concatenating the [codewords](../huffman-coding/code.md) of its symbols, where a one-leaf tree gives its symbol the one-bit codeword $0$. A bit string is decoded by parsing it into symbols along $T$ and lifting the decoded symbols to the leaf-symbol type; the decoder fails if parsing fails or a decoded symbol does not label a leaf.
