# Diffusion approximation for the stochastic SIR epidemic

**Diffusion approximation for the stochastic SIR epidemic** (Kurtz 1971;
Ethier–Kurtz 1986, ch. 11, Thm 2.3), with the law of large numbers and the martingale
functional CLT as hypotheses.

Let `x = (s, i)` solve the Kermack–McKendrick system in densities (`SIR.IsSolution β γ 1`), and
let `X N ω : ℝ → ℝ × ℝ` be measurable density paths. Assume, for every `δ > 0`,

* (law of large numbers) `P(∃ t ∈ [0, T], ‖X_N(t) - x(t)‖ ≥ δ) → 0`;
* (initial fluctuations) `P(‖U_N(0) - U₀‖ ≥ δ) → 0`, with `U₀` measurable;
* (martingale CLT, coupled form) `P(∃ t ∈ [0, T], ‖M_N(t) - M(t)‖ ≥ δ) → 0`, for a process
  `M` with continuous paths on `[0, T]` and measurable marginals;

and let `U` solve the linear fluctuation equation `U(t) = U₀ + (M(t) - M(0)) + ∫₀ᵗ DF(x) U`
pathwise.
Then the scaled fluctuations converge to `U` uniformly on `[0, T]` in probability:
`P(∃ t ∈ [0, T], ‖√N (X_N(t) - x(t)) - U(t)‖ ≥ ε) → 0` for every `ε > 0`. This event contains
the strict supremum event `sup > ε`; the non-strict supremum event `sup ≥ ε` is
`tendsto_measure_iSup_fluctuation_sub`.
