/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Extinction time of the subcritical stochastic SIS logistic epidemic

The stochastic SIS logistic epidemic in a population of size `N` is the continuous-time Markov
chain `X` on `{0, …, N}` (the number of infectives) with jumps `x → x + 1` at rate
`λ x (1 - x / N)` and `x → x - 1` at rate `μ x`. The state `0` is absorbing; `T_N` is its
hitting time. Brightwell, House and Luczak (2018, Theorem 1.1) showed that in the subcritical
regime, with `λ = λ(N)` and `μ = μ(N)` bounded away from `0` and `∞`,
`(μ - λ) √N → ∞` and a deterministic initial state with `X_N(0) (μ - λ) → ∞`,

  `(μ - λ) T_N - (log N + 2 log (μ - λ) - log (1 + (μ - λ) N / (λ X_N(0))) - log μ - log λ)`

converges in distribution to the standard Gumbel law `P(W ≤ w) = exp (-exp (-w))`
(`ProbabilityTheory.gumbelCDF 0 1 w`), and that
the corresponding expansion of `E T_N` holds with the Euler–Mascheroni constant (the mean of
`W`) as the constant term.

The chain is the continuous-time Markov chain of
`MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Path`, built from its rate matrix,
and `T_N` is `ProbabilityTheory.ctmcHittingTime`. The deterministic logistic SIS model is in
`Domains.Biology.Epidemiology.SIS`.

Sources: G. Brightwell, T. House and M. Luczak, "Extinction times in the subcritical
stochastic SIS logistic epidemic", J. Math. Biol. (2018), Theorem 1.1 and
Eq. (1.4) (arXiv:1312.7449).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.HittingTime
public import MathlibExt.Probability.Distributions.Gumbel
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace WantedExt.Biology.Epidemiology.SISLogisticExtinctionTimeWanted

open MeasureTheory ProbabilityTheory Filter Topology

/-- The rate matrix of the SIS logistic chain on the states `0, …, N`: from `x` the chain jumps
to `x + 1` at rate `λ x (1 - x / N)` and to `x - 1` at rate `μ x`; the diagonal entry is minus
the total rate. It is a rate matrix (`IsRateMatrix`) whenever `λ, μ ≥ 0`. -/
noncomputable def sisRateMatrix (N : ℕ) (lam mu : ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i j =>
    if (j : ℕ) = (i : ℕ) + 1 then lam * (i : ℝ) * (1 - (i : ℝ) / N)
    else if (j : ℕ) + 1 = (i : ℕ) then mu * (i : ℝ)
    else if j = i then -(lam * (i : ℝ) * (1 - (i : ℝ) / N) + mu * (i : ℝ))
    else 0

/-- The extinction time `T_N`: the hitting time of the absorbing state `0` by the SIS logistic
chain started at `x₀`, for the step sequence `ω` (valued in `ℝ≥0∞`). -/
noncomputable def extinctionTime (N : ℕ) (lam mu : ℝ) (x₀ : Fin (N + 1))
    (ω : ℕ → (Fin (N + 1) → Fin (N + 1)) × ℝ) : ENNReal :=
  ctmcHittingTime (sisRateMatrix N lam mu) x₀ {0} ω

/-- The centring of Brightwell, House and Luczak (2018, Eq. (1.4)):
`log N + 2 log (μ - λ) - log (1 + (μ - λ) N / (λ x₀)) - log μ - log λ`. -/
noncomputable def centring (N : ℕ) (lam mu : ℝ) (x₀ : ℕ) : ℝ :=
  Real.log N + 2 * Real.log (mu - lam) - Real.log (1 + (mu - lam) * N / (lam * x₀))
    - Real.log mu - Real.log lam

/-- **Gumbel limit of the extinction time.** Brightwell, House and Luczak (2018), Theorem 1.1 and
Eq. (1.4): let `λ(N)` and `μ(N)` be bounded away from `0` and `∞`, with `(μ - λ) √N → ∞`, and
let the initial states `x₀(N) ∈ {0, …, N}` be deterministic with `x₀(N) (μ - λ) → ∞`. Then for
every real `w`, the probability that `(μ - λ) T_N - centring` is at most `w` tends to
`exp (-exp (-w))`, the standard Gumbel distribution function `ProbabilityTheory.gumbelCDF 0 1 w`:
the centred and scaled extinction time converges in distribution to the standard Gumbel law.
(`hQ` records that each `sisRateMatrix` is a rate matrix, which holds since the rates are
nonnegative.)

Source: Brightwell, House and Luczak (2018), Theorem 1.1. -/
theorem_wanted tendsto_extinctionTime_gumbel (lam mu : ℕ → ℝ) (x₀ : (N : ℕ) → Fin (N + 1))
    (hQ : ∀ N, IsRateMatrix (sisRateMatrix N (lam N) (mu N)))
    (hbdd : ∃ c C : ℝ, 0 < c ∧ ∀ᶠ N in atTop,
      c ≤ lam N ∧ lam N ≤ C ∧ c ≤ mu N ∧ mu N ≤ C)
    (hgap : Tendsto (fun N : ℕ => (mu N - lam N) * Real.sqrt N) atTop atTop)
    (hinit : Tendsto (fun N : ℕ => ((x₀ N : ℕ) : ℝ) * (mu N - lam N)) atTop atTop)
    (w : ℝ) :
    Tendsto (fun N : ℕ => (ctmcInputMeasure (hQ N)).real
      {ω | (mu N - lam N) * (extinctionTime N (lam N) (mu N) (x₀ N) ω).toReal
          - centring N (lam N) (mu N) (x₀ N) ≤ w}) atTop (𝓝 (ProbabilityTheory.gumbelCDF 0 1 w))

/-- **Mean extinction time** (Brightwell, House and Luczak 2018, consequence of Theorem 1.1
stated after Eq. (1.4)). Under the hypotheses of `tendsto_extinctionTime_gumbel`,

  `E T_N = (centring + γ + o(1)) / (μ - λ)`,

where `γ` is the Euler–Mascheroni constant, the mean of the standard Gumbel law: the expected
centred and scaled extinction time tends to `γ`.

Source: Brightwell, House and Luczak (2018), Section 1.2. -/
theorem_wanted tendsto_mean_extinctionTime (lam mu : ℕ → ℝ) (x₀ : (N : ℕ) → Fin (N + 1))
    (hQ : ∀ N, IsRateMatrix (sisRateMatrix N (lam N) (mu N)))
    (hbdd : ∃ c C : ℝ, 0 < c ∧ ∀ᶠ N in atTop,
      c ≤ lam N ∧ lam N ≤ C ∧ c ≤ mu N ∧ mu N ≤ C)
    (hgap : Tendsto (fun N : ℕ => (mu N - lam N) * Real.sqrt N) atTop atTop)
    (hinit : Tendsto (fun N : ℕ => ((x₀ N : ℕ) : ℝ) * (mu N - lam N)) atTop atTop) :
    Tendsto (fun N : ℕ => (mu N - lam N) *
        (∫ ω, (extinctionTime N (lam N) (mu N) (x₀ N) ω).toReal ∂(ctmcInputMeasure (hQ N)))
      - centring N (lam N) (mu N) (x₀ N)) atTop (𝓝 Real.eulerMascheroniConstant)

end WantedExt.Biology.Epidemiology.SISLogisticExtinctionTimeWanted
