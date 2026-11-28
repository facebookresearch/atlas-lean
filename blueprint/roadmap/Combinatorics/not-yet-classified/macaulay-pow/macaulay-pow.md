# Macaulay's upper function

`Nat.macaulayPow d a` is `a^⟨d⟩`, and `a^⟨0⟩ = 0`. At level
`d + 1`, let `k` be the largest natural number with `C(k, d + 1) ≤ a`: the top term `C(k, d + 1)`
of the greedy binomial expansion of `a` is replaced by `C(k + 1, d + 2)`, and the remainder
`a - C(k, d + 1)` is treated at level `d`.
