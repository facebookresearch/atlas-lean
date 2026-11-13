# Exists admissible of prefix Free

Code-to-tree bridge: for a nonempty input with distinct symbols and a binary code that is
prefix-free on the input's symbols, some admissible tree (a full tree whose weighted leaves are a
permutation of the input) has weighted path length at most the code's cost
`Σ weight * (code symbol).length`, summed over `input`. The tree returned by `huffman` is one, by
`huffman_optimal_prefixFree`. Codewords of symbols outside the input are unconstrained, and no
codeword needs to be nonempty.
