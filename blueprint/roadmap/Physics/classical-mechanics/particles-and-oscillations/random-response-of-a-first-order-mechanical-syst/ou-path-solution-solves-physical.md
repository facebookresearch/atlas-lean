# The pathwise Ornstein–Uhlenbeck solution solves the damper equation

Let `c > 0`, let `k`, `σ` and `x₀` be real numbers, and let `w : ℝ → ℝ` be continuous. Then the
[pathwise Ornstein–Uhlenbeck solution](../../../../Probability/stochastic-calculus/ornstein-uhlenbeck-process/ou-path-solution.md) `X` with rate `k / c`, noise
amplitude `σ / c`, start `x₀` and driving path `w` satisfies, at every real time `t`,

`c (X(t) - x₀) = -k ∫₀ᵗ X(u) du + σ (w(t) - w(0))`,

the integral form of `c dx = -k x dt + σ dw`.
