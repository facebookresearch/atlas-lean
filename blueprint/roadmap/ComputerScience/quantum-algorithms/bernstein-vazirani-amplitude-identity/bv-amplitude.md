# Bernstein–Vazirani amplitude identity

Bernstein–Vazirani amplitude: for bitstrings `s t : Fin n → Bool` and a bit
`β`, with the phase oracle of the affine function `f x = (x · s) ⊕ β`, the
normalized sum `2⁻ⁿ ∑ₓ (-1) ^ (x · t) (-1) ^ f x` over all `x : Fin n →
Bool` equals `-1` if `t = s` and `β` is true, `1` if `t = s` and `β` is
false, and `0` if `t ≠ s`.
