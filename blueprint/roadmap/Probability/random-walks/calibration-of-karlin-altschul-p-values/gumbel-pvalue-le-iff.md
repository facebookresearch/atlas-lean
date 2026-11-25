# Rejection region of the Karlin–Altschul test

For `K > 0`, `θ > 0`, a natural number `n ≥ 1` and `0 < α < 1`, the
[Karlin–Altschul p-value](gumbel-pvalue.md) of a real score `s` is at most `α` if and only if `s` is
at least the Gumbel threshold: `1 - exp(-K n e^{-θ s}) ≤ α` if and only if
`log n / θ + x_α ≤ s`, where `x_α` is the [Gumbel level](gumbel-level.md).
