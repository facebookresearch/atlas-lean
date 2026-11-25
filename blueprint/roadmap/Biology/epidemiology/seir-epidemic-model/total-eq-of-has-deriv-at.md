# Conservation of S + E + I + R on an interval

Let `β`, `σ`, `γ`, `N` and `T` be real numbers, and suppose that `S, E, I, R : ℝ → ℝ` satisfy the
four SEIR equations

`S' = -β S I / N`,   `E' = β S I / N - σ E`,   `I' = σ E - γ I`,   `R' = γ I`

with two-sided derivatives at every time `t` with `0 ≤ t ≤ T`, the quotient `β S I / N` being read
as `0` when `N = 0`. Then for every such `t`,

`S(t) + E(t) + I(t) + R(t) = S(0) + E(0) + I(0) + R(0)`.
