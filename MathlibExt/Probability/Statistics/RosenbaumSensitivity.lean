/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Treatment probabilities in Rosenbaum's matched-pair model -/

namespace WantedExt.Probability.Statistics.RosenbaumSensitivityWanted

/-- **Treatment probabilities under bounded hidden bias.** For `γ ≥ 0` and unobserved covariates
`u₁, u₂ ∈ [0, 1]`, the probability `exp(γ u₁) / (exp(γ u₁) + exp(γ u₂))` that the first unit of a
pair is treated lies in `[1 / (1 + Γ), Γ / (1 + Γ)]` with `Γ = exp γ`.

Sources: P. R. Rosenbaum, "Sensitivity analysis for certain permutation inferences in matched
observational studies", Biometrika 74 (1987) 13–26; P. R. Rosenbaum, *Observational Studies*, 2nd
ed., Springer (2002). -/
public theorem treatmentProb_mem {γ u₁ u₂ : ℝ} (hγ : 0 ≤ γ) (hu₁ : 0 ≤ u₁) (hu₁' : u₁ ≤ 1)
    (hu₂ : 0 ≤ u₂) (hu₂' : u₂ ≤ 1) :
    1 / (1 + Real.exp γ) ≤ Real.exp (γ * u₁) / (Real.exp (γ * u₁) + Real.exp (γ * u₂)) ∧
      Real.exp (γ * u₁) / (Real.exp (γ * u₁) + Real.exp (γ * u₂)) ≤
        Real.exp γ / (1 + Real.exp γ) := by
  have exp_le (u v : ℝ) (hu : u ≤ 1) (hv : 0 ≤ v) :
      Real.exp (γ * u) ≤ Real.exp γ * Real.exp (γ * v) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h₁ := mul_le_mul_of_nonneg_left hu hγ
    have h₂ := mul_nonneg hγ hv
    linarith
  have hsum : 0 < Real.exp (γ * u₁) + Real.exp (γ * u₂) := by positivity
  have hΓ : 0 < 1 + Real.exp γ := by positivity
  constructor
  · rw [div_le_div_iff₀ hΓ hsum]
    linarith only [exp_le u₂ u₁ hu₂' hu₁]
  · rw [div_le_div_iff₀ hsum hΓ]
    linarith only [exp_le u₁ u₂ hu₁' hu₂]

end WantedExt.Probability.Statistics.RosenbaumSensitivityWanted
