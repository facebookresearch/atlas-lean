# Ctr Encrypt

Randomized counter-mode encryption (Katz and Lindell, Section 3.6.2, over an additive group
of blocks): with initial counter `ctr`, the ciphertext is
`(ctr, m + keystream)`. The keystream starts at `ctr` itself rather than at `ctr + 1`.
