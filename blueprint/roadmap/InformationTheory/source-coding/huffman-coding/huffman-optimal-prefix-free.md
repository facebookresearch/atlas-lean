# Huffman optimal prefix Free

The tree returned by `huffman` has weighted path length at most the cost
`Σ weight * (code symbol).length`, summed over `input`, of every binary code that is prefix-free
on the input's symbols. Codewords of symbols outside the input are unconstrained, so this covers
in particular every code that is prefix-free on all of `α`. No codeword needs to be nonempty: for
a one-symbol input the weighted path length is zero.
