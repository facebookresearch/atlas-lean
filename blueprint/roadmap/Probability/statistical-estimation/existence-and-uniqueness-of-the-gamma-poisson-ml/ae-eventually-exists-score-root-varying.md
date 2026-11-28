# Cramér consistency of joint score roots with random size factors

On a probability space `(Ω, μ)`, let `(S₀, X₀), (S₁, X₁), …` be pairs of measurable random
variables, a size factor `Sᵢ` with `Sᵢ(ω) > 0` for every `ω` and a count `Xᵢ` with values in `ℕ`.
Assume the pairs are pairwise independent (`(Sᵢ, Xᵢ)` and `(Sⱼ, Xⱼ)` are independent for `i ≠ j`)
and identically distributed, and `X₀` is integrable. Assume also that `S₀` is integrable, and let
`a₀ > 0` and `b₀ > 0` solve the population rate equation `R(a₀, b₀) = 0`, where `R` is the
[population rate score](pop-rate-score-log.md) and `G` the
[population shape score](pop-shape-score.md) of `(S₀, X₀)`. Assume the sign condition, a local
identifiability of the shape: for every sufficiently small `η > 0` there is `c > 0` with
`R(a₀ - η, c) > 0` and `G(a₀ - η, c) > 0`, and there is `c' > 0` with `R(a₀ + η, c') < 0` and
`G(a₀ + η, c') < 0`.

Then, almost surely, for every `ε > 0` and all large `n`, the joint score equations of the first `n`
cells (the counts `X₀(ω), …, X₍ₙ₋₁₎(ω)` at the size factors `S₀(ω), …, S₍ₙ₋₁₎(ω)`) have a solution
`(â, b̂)` with `â > 0`, `b̂ > 0`, `|â - a₀| < ε` and `|b̂ - b₀| < ε`: the
[shape score](../likelihood-equations-and-efficiency-of-the-gamma/shape-score.md) `∂ℓ/∂a` and the
[rate score](../likelihood-equations-and-efficiency-of-the-gamma/rate-score.md) `∂ℓ/∂b` both vanish
at `(â, b̂)`, where `ℓ` is the
[log marginal likelihood](../likelihood-equations-and-efficiency-of-the-gamma/log-marginal-lik.md)
of these cells (Cramér 1946). The sign condition is a hypothesis; `R(a₀, b₀) = 0` holds, for
example, under a [matching conditional mean](pop-rate-score-log-eq-zero-of-cond-mean.md).
