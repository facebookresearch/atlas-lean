# Generator of the Λ-coalescent block-counting process

The generator of the **block-counting process** of the Λ-coalescent on the states
`0, …, n` (state `b` means `b` blocks): from `b` blocks the process jumps to `j < b` blocks at
rate `(b.choose (b + 1 - j)) λ_{b, b + 1 - j}` (a `(b + 1 - j)`-merger), and the diagonal is
`-λ_b`. States `0` and `1` are absorbing (state `0` is never reached from `b ≥ 1`).
