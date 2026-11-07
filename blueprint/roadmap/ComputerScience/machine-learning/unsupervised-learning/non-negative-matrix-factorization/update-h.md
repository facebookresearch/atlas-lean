# Lee–Seung multiplicative update of H

The Lee–Seung multiplicative update of `H` (Lee and Seung 2001, Theorem 1):
`H a j ← H a j * (Wᵀ X) a j / (Wᵀ W H) a j`. An entry with a zero denominator becomes `0`
(Lean's `x / 0 = 0`).
