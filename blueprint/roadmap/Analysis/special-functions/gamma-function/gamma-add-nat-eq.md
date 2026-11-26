# Shifting the Gamma function by a natural number

`Γ(a + k) = a⁽ᵏ⁾ Γ(a)`, with `a⁽ᵏ⁾ = a (a + 1) ⋯ (a + k - 1)` the ascending Pochhammer
symbol, provided `a + j ≠ 0` for every natural `j < k` (for instance when `0 < a`). Only the
shifts `a, a + 1, …, a + k - 1` that the recursion passes through are constrained, so `a` may
be a nonpositive integer as long as `a + k ≤ 0`. Here `Γ` is Mathlib's real Gamma function, which is `0` at the poles `0, -1, -2, …`: for `a = -2` and `k = 1` the identity reads `0 = (-2) · 0`, not an equation between finite classical values. For `a > 0` both sides are classical values.
