# Message Poly

The message polynomial of an MSB-first payload of declared length `l = bits.length`:
`m = ∑_j bit_j * X^(l-1-j)`. Leading zeros are counted in `l`.
