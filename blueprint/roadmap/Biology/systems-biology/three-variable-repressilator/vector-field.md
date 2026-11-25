# Right-hand side of the three-variable repressilator

For `n ∈ ℕ`, a real `α` and `x = (x₀, x₁, x₂) ∈ ℝ³`, the repressilator field is
`F(x)_i = α / (1 + x_{i−1}ⁿ) − x_i` for `i = 0, 1, 2`, with indices mod 3: gene `i − 1` represses
gene `i`. With the convention `x / 0 = 0`, the repression term is `0` when `x_{i−1}ⁿ = −1` (`n` odd
and `x_{i−1} = −1`). In the model the protein concentrations are nonnegative and the transcription
rate `α` is positive. The system `x' = F(x)` is the protein-only reduction of the Elowitz–Leibler
repressilator, with the mRNAs at quasi-steady state, no leak, `α` the maximal dimensionless
transcription rate and `n` the Hill coefficient.
