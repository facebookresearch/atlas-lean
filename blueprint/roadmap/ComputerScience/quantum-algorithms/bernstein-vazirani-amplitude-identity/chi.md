# Sign character of bitstrings

For bitstrings `x s : Fin n → Bool` (with `true` for the bit `1`), `chi x s`
is the complex number `(-1) ^ (x · s)`, where `x · s` is the number of
positions at which both `x` and `s` are `1`. Equivalently, it is the
Boolean-cube character of the support of `s`, evaluated at the bitwise
complement of `x`, where the cube reads `true` as `1` and `false` as `-1`.
