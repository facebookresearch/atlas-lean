# Closed-form trajectory of the shifted Riccati equation

For real `c`, `q`, `L`, `p₀` and `t`,
`R(t) = q + L (p₀ - q) / ((L + c (p₀ - q)) e^{L t} - c (p₀ - q))`. For `L ≠ 0`: `R(0) = p₀`, and on
any interval containing `0` on which the denominator does not vanish, `u = R - q` solves the Riccati
equation `u' = -L u - c u²` with `u(0) = p₀ - q`.

With the convention `x / 0 = 0`, `R(t) = q` at any `t` where the denominator vanishes (where that
solution blows up), and for `L = 0` the formula gives `R(t) = q` for every `t`.
