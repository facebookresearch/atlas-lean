# A continuous solution of the damper equation is the pathwise solution

Let `c > 0`, let `k`, `σ` and `x₀` be real numbers, and let `w, x : ℝ → ℝ` be continuous with

`c (x(t) - x₀) = -k ∫₀ᵗ x(u) du + σ (w(t) - w(0))` for every `t ≥ 0`.

Then for every `t ≥ 0`, `x(t)` equals the
[pathwise Ornstein–Uhlenbeck solution](../../../../Probability/stochastic-calculus/ornstein-uhlenbeck-process/ou-path-solution.md) with rate `k / c`, noise amplitude
`σ / c`, start `x₀` and driving path `w`, evaluated at `t`.
