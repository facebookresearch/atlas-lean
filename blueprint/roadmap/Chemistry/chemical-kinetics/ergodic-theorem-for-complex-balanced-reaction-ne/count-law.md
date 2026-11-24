# Measure on molecule counts with a given mass function

For a set `S` and a function `p : ℕ^S → ℝ`, this is the measure on `ℕ^S` (with its product
σ-algebra) that puts mass `max(p(x), 0)` at each state `x`:

`μ_p = ∑_{x ∈ ℕ^S} max(p(x), 0) δ_x`, that is `μ_p(A) = ∑_{x ∈ A} max(p(x), 0)` for every
measurable set `A`.

Negative values of `p` count as `0`, and the total mass `∑_x max(p(x), 0)` can be any value in
`[0, ∞]`. When `p ≥ 0` and `∑_x p(x) = 1`, `μ_p` is a probability measure, and for finite `S` it
is the law with mass function `p`: `μ_p({x}) = p(x)`.
