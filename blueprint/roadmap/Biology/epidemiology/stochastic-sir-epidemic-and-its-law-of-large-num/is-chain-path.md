# One sample path of the stochastic SIR chain

**One sample path of the stochastic SIR chain** of population size `N` (Kurtz's random
time-change representation; Ethier–Kurtz 1986, ch. 6, (4.1) and ch. 11, (2.1)). Given the
paths `y₁`, `y₂` of the two driving unit-rate counting processes, the counts `S, I, R : ℝ → ℕ`
satisfy, for `t ≥ 0`,

`S(t) = S(0) - y₁(∫₀ᵗ β S I / N)`,
  `I(t) = I(0) + y₁(∫₀ᵗ β S I / N) - y₂(∫₀ᵗ γ I)`,
  `R(t) = R(0) + y₂(∫₀ᵗ γ I)`,

with `S(0) + I(0) + R(0) = N`. When `y₁`, `y₂` are independent unit-rate Poisson processes,
this is the continuous-time Markov chain that jumps `(S, I, R) → (S - 1, I + 1, R)` at rate
`β S I / N` (infection) and `(S, I, R) → (S, I - 1, R + 1)` at rate `γ I` (recovery). The
counts are natural numbers, so they are nonnegative by construction. The paths are required to
be measurable (a càdlàg path is), so that the clocks are genuine Lebesgue integrals.
