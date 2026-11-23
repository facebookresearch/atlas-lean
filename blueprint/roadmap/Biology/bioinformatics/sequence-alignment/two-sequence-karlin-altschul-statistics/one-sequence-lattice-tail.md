# Lattice one-sequence tail hypothesis for the maximal segment score

For real weights and scores `q` and `f` on a finite alphabet and real constants `θ`, `K` and `h`,
the lattice one-sequence tail holds when `P(M_L > t) = (K + o(1)) L e^{-θ t⁺}`, uniformly as
`L → ∞` and `L e^{-θ t} → 0` over thresholds `t ≤ η L`. Here `P(M_L > t)` is the
[score probability](../../../../Probability/random-walks/maximal-segment-score-of-a-random-sequence/score-prob.md) that the
[maximal segment score](../../../../Probability/random-walks/maximal-segment-score-of-a-random-sequence/max-seg-score.md) of the
scores of `L` letters exceeds `t`, and `t⁺ = (⌊t / h⌋ + 1) h` is the
[lattice point](lattice-above.md) of `t`, for a positive span `h > 0` the next point of `hℤ` above
`t`. Precisely: for every `ε > 0` there are `L₀`, `δ > 0` and `η > 0` such that
`|P(M_L > t) - K L e^{-θ t⁺}| ≤ ε L e^{-θ t⁺}` for all `L ≥ L₀` and all real `t` with
`L e^{-θ t} ≤ δ` and `t ≤ η L`. It is the [one-sequence tail](one-sequence-tail.md) with
`e^{-θ t}` replaced by `e^{-θ t⁺}` on the right, the form of the lattice case of Karlin and Dembo
(1992) for a positive span, and an assumption on `(q, f)`, not derived from them. When `q` is a
probability vector the score probabilities are probabilities for `L` independent letters of law
`q`.
