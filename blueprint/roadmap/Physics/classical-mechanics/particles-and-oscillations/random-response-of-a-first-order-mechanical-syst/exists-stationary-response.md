# For c, k > 0, a pathwise stationary response exists

Let `c > 0`, `k > 0` and `σ` real. There are a probability measure `μ` on the paths
`ℝ≥0 → ℝ`, a process `B` and a random variable `X₀` on that path space such that:

- `B` is a standard Brownian motion under `μ` (Brownian finite-dimensional laws and almost surely
  continuous paths);
- `X₀` has the Gaussian law `N(0, σ² / (2 c k))` and is independent of `B`;
- for almost every path `ω` and every real `t`, the
  [pathwise Ornstein–Uhlenbeck solution](../../../../Probability/stochastic-calculus/ornstein-uhlenbeck-process/ou-path-solution.md) `X(t, ω)` with rate `k / c`,
  noise amplitude `σ / c`, start `X₀(ω)` and driving path `w(u) = B(max(u, 0), ω)` satisfies
  `c (X(t, ω) - X₀(ω)) = -k ∫₀ᵗ X(u, ω) du + σ (w(t) - w(0))`;
- the process `t ↦ X(t, ·)`, `t ≥ 0`, is a
  [stationary Ornstein–Uhlenbeck process](../../../../Probability/stochastic-calculus/ornstein-uhlenbeck-process/is-stationary-ornstein-uhlenbeck.md) with rate `k / c`
  and noise amplitude `σ / c`.
