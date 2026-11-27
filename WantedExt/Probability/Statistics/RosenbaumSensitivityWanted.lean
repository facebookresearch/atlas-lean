/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Rosenbaum's sensitivity bounds for the matched-pair sign test

In a matched-pair observational study, Rosenbaum's model of hidden bias lets the odds that the
first unit of pair `i` receives treatment be `exp(γ (u_{i1} - u_{i2}))` for unobserved covariates
`u ∈ [0, 1]` and a sensitivity parameter `Γ = exp γ ≥ 1`. The probability `π_i` that the first
unit is treated then lies in `[1 / (1 + Γ), Γ / (1 + Γ)]`, so the within-pair treatment odds lie
in `[1 / Γ, Γ]`; `Γ = 1` is a randomized experiment.

Under the sharp null hypothesis of no treatment effect, the sign statistic, the number of
untied pairs in which the treated unit has the larger response, is a sum of independent
Bernoulli variables with success probabilities `π_i` (one of `π_i`, `1 - π_i` per pair, both in
the same interval). Its upper tail is the Poisson-binomial tail `poissonBinomialTail π k` of
`MathlibExt.Probability.Distributions.PoissonBinomial`, which is nondecreasing in each `π_i`
(`poissonBinomialTail_mono`), so it lies between the tails of the binomial laws
`Bin(n, 1 / (1 + Γ))` and `Bin(n, Γ / (1 + Γ))` (`upperTail_bounds`). These two tails bound the
p-value of the sign test for every `Γ ≥ 1`.

Sources: P. R. Rosenbaum, "Sensitivity analysis for certain permutation inferences in matched
observational studies", Biometrika 74 (1987) 13–26; P. R. Rosenbaum, *Observational Studies*,
2nd ed., Springer (2002), §4.3.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Exp
public import MathlibExt.Probability.Distributions.PoissonBinomial
public import MathlibExt.Probability.Statistics.RosenbaumSensitivity

@[expose] public section

namespace WantedExt.Probability.Statistics.RosenbaumSensitivityWanted

open ProbabilityTheory

/-- **Binomial bounds on the sign-test tail.** Let `Γ ≥ 1`, and let the success probabilities
`π_i`, `i < n`, of independent Bernoulli variables `B_i` satisfy
`1 / (1 + Γ) ≤ π_i ≤ Γ / (1 + Γ)` for every `i`. Then for every `k`,
`P(Bin(n, 1 / (1 + Γ)) ≥ k) ≤ P(∑ᵢ Bᵢ ≥ k) ≤ P(Bin(n, Γ / (1 + Γ)) ≥ k)`, where
`P(∑ᵢ Bᵢ ≥ k)` is the Poisson-binomial upper tail `poissonBinomialTail π k` and the binomial tails
are the Poisson-binomial tails with constant success probabilities.

Sources: P. R. Rosenbaum, "Sensitivity analysis for certain permutation inferences in matched
observational studies", Biometrika 74 (1987) 13–26; P. R. Rosenbaum, *Observational Studies*, 2nd
ed., Springer (2002), §4.3. -/
public theorem upperTail_bounds {n : ℕ} {Γ : ℝ} (hΓ : 1 ≤ Γ) (π : Fin n → ℝ)
    (hlo : ∀ i, 1 / (1 + Γ) ≤ π i) (hhi : ∀ i, π i ≤ Γ / (1 + Γ)) (k : ℕ) :
    poissonBinomialTail (fun _ : Fin n => 1 / (1 + Γ)) k ≤ poissonBinomialTail π k ∧
      poissonBinomialTail π k ≤ poissonBinomialTail (fun _ : Fin n => Γ / (1 + Γ)) k := by
  have hpos : (0 : ℝ) < 1 + Γ := by linarith
  have hlo₀ : 0 ≤ 1 / (1 + Γ) := by positivity
  have hlo₁ : 1 / (1 + Γ) ≤ 1 := (div_le_one₀ hpos).mpr (by linarith)
  have hhi₀ : 0 ≤ Γ / (1 + Γ) := div_nonneg (by linarith) hpos.le
  have hhi₁ : Γ / (1 + Γ) ≤ 1 := (div_le_one₀ hpos).mpr (by linarith)
  have hπ : ∀ i, π i ∈ Set.Icc (0 : ℝ) 1 := fun i => ⟨hlo₀.trans (hlo i), (hhi i).trans hhi₁⟩
  exact ⟨poissonBinomialTail_mono (fun _ => ⟨hlo₀, hlo₁⟩) hπ hlo k,
    poissonBinomialTail_mono hπ (fun _ => ⟨hhi₀, hhi₁⟩) hhi k⟩

end WantedExt.Probability.Statistics.RosenbaumSensitivityWanted
