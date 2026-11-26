# Product formula for the sign character

For bitstrings `x s : Fin n → Bool`, `chi x s` is the product over positions
`i` of `-1` when `s i` and `x i` are both true, and `1` otherwise. Hence
`chi x s = (-1) ^ (x · s)`.
