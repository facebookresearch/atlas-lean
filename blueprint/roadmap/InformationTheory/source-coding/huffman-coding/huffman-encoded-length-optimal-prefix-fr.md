# Huffman encoded Length optimal prefix Free

The tree returned by `huffman` has `encodedLength` at most the cost
`Σ weight * (code symbol).length`, summed over `input`, of every binary code that is prefix-free
on the input's symbols and gives each input symbol of positive weight a nonempty codeword. That
hypothesis matters only for a one-symbol input of positive weight, where the bound fails for the
empty codeword: `encodedLength` charges the encoder's one-bit codeword `[false]`, while the empty
codeword is prefix-free on one symbol and costs zero. A one-symbol input of weight zero needs no
nonempty codeword, since both sides are zero, and with two or more distinct input symbols
prefix-freeness already makes every input codeword nonempty.
`HuffmanTree.encodedLength_eq_sum_codeLengths` states when `encodedLength` is the encoder's
emitted cost.
