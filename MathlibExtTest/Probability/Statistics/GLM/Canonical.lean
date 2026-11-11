/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GLM.Canonical

@[expose] public section

open Finset Real Matrix
open MathlibExt.Probability.Statistics.GLM

namespace MathlibExtTest.Probability.Statistics.GLM

/-- Intercept plus one covariate `x = (0, 1)`. -/
noncomputable def X₀ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of ![![1, 0], ![1, 1]]

theorem X₀_mulVec_injective : Function.Injective X₀.mulVec := by
  intro β γ h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [X₀, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  funext k
  fin_cases k
  · exact h0
  · simp only [Fin.mk_one, Fin.isValue]
    linarith

/-- `σ'(0) = 1 / 4`, from Mathlib's derivative of `Real.sigmoid`. -/
example : HasDerivAt sigmoid (1 / 4) 0 := by
  convert hasDerivAt_sigmoid 0 using 1
  norm_num

/-- The linear predictor adds the offset to `X β`. -/
example : linearPredictor X₀ ![1, 2] ![3, 4] = ![4, 9] := by
  ext i
  fin_cases i <;> simp [linearPredictor_apply, X₀, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    norm_num

/-- The per-observation identity at `y = 1 / 2` (non-binary responses are allowed). -/
example (η : ℝ) :
    (1 / 2) * log (sigmoid η) + (1 - 1 / 2) * log (1 - sigmoid η) =
      (1 / 2) * η - log (1 + exp η) :=
  sigmoid_logLik_term _ _

/-- Logistic score at `β = 0`, `y = (1, 0)`: `μ = (1/2, 1/2)`, `Xᵀ (y - μ) = (0, -1/2)`. -/
example : HasFDerivAt (logisticLogLik X₀ 0 ![1, 0]) (Real.dotL ![0, -1 / 2]) 0 := by
  have e : (![0, -1 / 2] : Fin 2 → ℝ) =
      X₀.transpose *ᵥ (![1, 0] - sigmoid ∘ linearPredictor X₀ 0 0) := by
    ext j
    fin_cases j <;>
      simp [X₀, linearPredictor_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  rw [e]
  exact hasFDerivAt_logisticLogLik X₀ 0 ![1, 0] 0

/-- Poisson score at `β = 0`, `y = (2, 0)`: `exp η = (1, 1)`, `Xᵀ (y - exp η) = (0, -1)`. -/
example : HasFDerivAt (poissonLogLik X₀ 0 ![2, 0]) (Real.dotL ![0, -1]) 0 := by
  have e : (![0, -1] : Fin 2 → ℝ) =
      X₀.transpose *ᵥ (![2, 0] - exp ∘ linearPredictor X₀ 0 0) := by
    ext j
    fin_cases j <;>
      simp [X₀, linearPredictor_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    norm_num
  rw [e]
  exact hasFDerivAt_poissonLogLik X₀ 0 ![2, 0] 0

/-- Logistic curvature at `β = 0` along the covariate direction: `-(1/4) · 1`. -/
example : deriv^[2] (fun t : ℝ => logisticLogLik X₀ 0 ![1, 0] (0 + t • ![0, 1])) 0 = -1 / 4 := by
  rw [deriv2_logisticLogLik_line]
  simp [X₀, linearPredictor_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  norm_num

/-- Poisson curvature at `β = 0` along the covariate direction: `-exp 0 · 1`. -/
example : deriv^[2] (fun t : ℝ => poissonLogLik X₀ 0 ![2, 0] (0 + t • ![0, 1])) 0 = -1 := by
  rw [deriv2_poissonLogLik_line]
  simp [X₀, linearPredictor_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

example : ConcaveOn ℝ Set.univ (logisticLogLik X₀ 0 ![1, 0]) := concaveOn_logisticLogLik _ _ _

example : ConcaveOn ℝ Set.univ (poissonLogLik X₀ 0 ![2, 0]) := concaveOn_poissonLogLik _ _ _

/-- Uniqueness applied to the full-rank fixture. -/
example {β₁ β₂ : Fin 2 → ℝ} (h₁ : IsMaxOn (logisticLogLik X₀ 0 ![1, 0]) Set.univ β₁)
    (h₂ : IsMaxOn (logisticLogLik X₀ 0 ![1, 0]) Set.univ β₂) : β₁ = β₂ :=
  logisticLogLik_maximizer_unique X₀ 0 _ X₀_mulVec_injective h₁ h₂

example {β₁ β₂ : Fin 2 → ℝ} (h₁ : IsMaxOn (poissonLogLik X₀ 0 ![2, 0]) Set.univ β₁)
    (h₂ : IsMaxOn (poissonLogLik X₀ 0 ![2, 0]) Set.univ β₂) : β₁ = β₂ :=
  poissonLogLik_maximizer_unique X₀ 0 _ X₀_mulVec_injective h₁ h₂

/-- Separation fixture: `ℓ(0) = -2 log 2`. -/
example : logisticLogLik separationDesign 0 ![0, 1] 0 = -2 * log 2 := by
  rw [logisticLogLik_separation]
  norm_num [one_add_one_eq_two]

/-- Separation fixture: `ℓ(0) < ℓ(1) < 0`. -/
example : logisticLogLik separationDesign 0 ![0, 1] 0 <
      logisticLogLik separationDesign 0 ![0, 1] 1 ∧
    logisticLogLik separationDesign 0 ![0, 1] 1 < 0 := by
  refine ⟨?_, logisticLogLik_separation_neg 1⟩
  simpa using logisticLogLik_separation_lt 0

example (β : Fin 1 → ℝ) : ¬ IsMaxOn (logisticLogLik separationDesign 0 ![0, 1]) Set.univ β :=
  logisticLogLik_separation_not_isMaxOn β

/-- All-zero counts over three observations: no Poisson maximizer. -/
example (β : Fin 1 → ℝ) :
    ¬ IsMaxOn (poissonLogLik (Matrix.of fun (_ : Fin 3) (_ : Fin 1) => (1 : ℝ)) 0 0) Set.univ β :=
  poissonLogLik_allZero_not_isMaxOn β

example : poissonLogLik (Matrix.of fun (_ : Fin 3) (_ : Fin 1) => (1 : ℝ)) 0 0 0 = -3 := by
  rw [poissonLogLik_allZero]
  simp

/-- The saturated term is not identically zero: `-H(1/2) = -log 2`. -/
example : logisticLogLikSaturated (![2⁻¹] : Fin 1 → ℝ) = -log 2 := by
  simp [logisticLogLikSaturated]

example : logisticLogLikSaturated (![1, 0] : Fin 2 → ℝ) = 0 :=
  logisticLogLikSaturated_eq_zero _ fun i => by fin_cases i <;> simp

/-- Deviance at `β = 0` for `y = (1, 0)`: `ℓ(0) = -2 log 2`, so `D = 4 log 2 > 0`. -/
example : logisticDeviance X₀ 0 ![1, 0] 0 = 4 * log 2 := by
  rw [logisticDeviance_eq X₀ 0 _ fun i => by fin_cases i <;> simp]
  simp [logisticLogLik, linearPredictor_apply]
  norm_num [one_add_one_eq_two]
  ring

example (β : Fin 2 → ℝ) : 0 ≤ logisticDeviance X₀ 0 ![1, 0] β :=
  logisticDeviance_nonneg X₀ 0 _ (fun i => by fin_cases i <;> simp) β

example (η : ℝ) : 1 * η - log (1 + exp η) < 0 := logisticTerm_neg (Or.inr rfl) η

end MathlibExtTest.Probability.Statistics.GLM
