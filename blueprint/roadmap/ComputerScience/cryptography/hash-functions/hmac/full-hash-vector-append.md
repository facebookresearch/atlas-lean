# Hashing a one-block prefix

Let `0 < n`. For an initial value `iv`, an `n`-bit block `v` and a bit string
`m`, the full hash of `v ++ m` from `iv` equals the continuation hash of `m`
from the chaining value `h (iv, v)`.
