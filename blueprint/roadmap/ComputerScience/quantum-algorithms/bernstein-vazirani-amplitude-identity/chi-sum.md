# Orthogonality of the sign characters

Character orthogonality: for bitstrings `s t : Fin n → Bool`, the sum over
all `x : Fin n → Bool` of `chi x s * chi x t` equals `2 ^ n` when `s = t`
and `0` otherwise.
