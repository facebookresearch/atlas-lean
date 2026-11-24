# Susceptibles in integrating-factor form on an interval

Let `β`, `σ`, `γ`, `N` and `T` be real numbers, and suppose that `S, E, I, R : ℝ → ℝ` satisfy the
four SEIR equations

`S' = -β S I / N`,   `E' = β S I / N - σ E`,   `I' = σ E - γ I`,   `R' = γ I`

with two-sided derivatives at every time `t` with `0 ≤ t ≤ T`. Then for every such `t`,

`S(t) = S(0) exp(-∫₀ᵗ β I(s) / N ds)`.

Here `β I(s) / N` is read as `0` when `N = 0`, and then `S(t) = S(0)`. For `T < 0` there is no such
time.
