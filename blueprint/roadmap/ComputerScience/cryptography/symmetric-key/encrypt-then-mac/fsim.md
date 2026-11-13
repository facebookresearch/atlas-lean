# Fsim

The MAC forger's simulation of the CCA game (continuation-passing): encryption queries are
encrypted with `k₁` and tagged through the MAC oracle; decryption queries are answered by
`simDec`; the forger stops at the query with index `j` if it is a decryption query and outputs
that ciphertext as its forgery.
