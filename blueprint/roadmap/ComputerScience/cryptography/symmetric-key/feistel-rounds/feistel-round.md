# Feistel Round

One Feistel round with round function `f`, as a permutation of the block space: it maps
`(l, r)` to `(r, l xor f r)`, and its inverse maps `(a, b)` to `(b xor f a, a)`.
