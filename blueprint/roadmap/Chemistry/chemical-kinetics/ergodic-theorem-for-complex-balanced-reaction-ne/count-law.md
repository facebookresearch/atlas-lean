# Measure on molecule counts with a given mass function

For a set `S` and a function `p : ℕ^S → ℝ`, this is the measure on `ℕ^S` (with its product
σ-algebra) that puts mass `max(p(x), 0)` at each state `x`:

`μ_p = ∑_{x ∈ ℕ^S} max(p(x), 0) δ_x`, that is `μ_p(A) = ∑_{x ∈ A} max(p(x), 0)` for every
measurable set `A`.

Negative values of `p` count as `0`, and the total mass `∑_x max(p(x), 0)` can be any value in
`[0, ∞]`. For finite `S` and a probability mass function `p` (`p ≥ 0` and `∑_x p(x) = 1`), the
[integral](integral-count-law.md) of a bounded function `f` against `μ_p` is `∑_x p(x) f(x)`.
