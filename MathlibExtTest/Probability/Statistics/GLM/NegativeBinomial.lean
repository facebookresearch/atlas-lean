/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GLM.NegativeBinomial

@[expose] public section

open Finset Real Matrix ProbabilityTheory
open MathlibExt.Probability.Statistics.GLM.NegativeBinomial

namespace MathlibExtTest.Probability.Statistics.GLM.NegativeBinomial

/-! ### Scalar kernel at `θ = 1`, `η = 0` (mean `μ = 1`) -/

theorem nbScore_one_three_zero : nbScore 1 3 0 = 1 := by norm_num [nbScore]

/-- The score `θ (y - μ) / (θ + μ) = 1 · (3 - 1) / 2 = 1` is the derivative of the kernel. -/
example : HasDerivAt (nbKernel 1 3) 1 0 := by
  simpa [nbScore_one_three_zero] using hasDerivAt_nbKernel one_pos 3 0

theorem nbObsWeight_one_three_zero : nbObsWeight 1 3 0 = 1 := by norm_num [nbObsWeight]

/-- The second derivative `-θ (y + θ) μ / (θ + μ)² = -1 · 4 · 1 / 4 = -1`. -/
example : HasDerivAt (nbScore 1 3) (-1) 0 := by
  simpa [nbObsWeight_one_three_zero] using hasDerivAt_nbScore one_pos 3 0

/-- The Fisher weight `θ μ / (θ + μ) = 1 / 2` differs from the observed weight `1` at `y = 3`. -/
example : nbFisherWeight 1 0 = 1 / 2 := by norm_num [nbFisherWeight]

example : nbObsWeight 1 3 0 ≠ nbFisherWeight 1 0 := by
  norm_num [nbObsWeight, nbFisherWeight]

/-- The observed weight at the count `y = 0` is still positive. -/
example : 0 < nbObsWeight 1 0 0 := nbObsWeight_pos one_pos (by norm_num) 0

/-- Under `y ~ NB(1, 1)` the observed weight averages to the Fisher weight `1 / 2`. -/
example : HasSum (fun k : ℕ => nbObsWeight 1 k 0 * negBinomialReal 1 (exp 0) k) (1 / 2) := by
  have h := hasSum_nbObsWeight_mul_negBinomialReal one_pos 0
  rwa [show nbFisherWeight 1 0 = 1 / 2 by norm_num [nbFisherWeight]] at h

example : HasSum (fun k : ℕ => nbScore 1 k 0 * negBinomialReal 1 (exp 0) k) 0 :=
  hasSum_nbScore_mul_negBinomialReal one_pos 0

/-! ### The kernel at a count, against the mass function -/

/-- `nbKernel 1 2 0 = 2 · 0 - 3 log 2`. -/
theorem nbKernel_one_two_zero : nbKernel 1 2 0 = -(3 * log 2) := by
  norm_num [nbKernel]

/-- `NB(2; 1, 1) = 1⁽²⁾ / 2! · (1 / 2) · (1 / 2)² = 1 / 8`. -/
theorem negBinomialReal_one_one_two : negBinomialReal 1 (exp 0) 2 = 1 / 8 := by
  norm_num [negBinomialReal, ascPochhammer_succ_eval]

/-- At `θ = 1` the constant `log (1⁽²⁾ / 2!) + 1 · log 1` vanishes, so the log mass is the kernel:
`log (1 / 8) = -3 log 2`. -/
example : log (negBinomialReal 1 (exp 0) 2) = nbKernel 1 2 0 := by
  rw [log_negBinomialReal_exp one_pos]
  norm_num [ascPochhammer_succ_eval]

example : log (negBinomialReal 1 (exp 0) 2) = -(3 * log 2) := by
  rw [negBinomialReal_one_one_two, ← nbKernel_one_two_zero, nbKernel]
  norm_num
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, one_div, log_inv, log_pow]
  ring

/-! ### The mean scale -/

/-- At `y = 0`, `θ = μ = 1` the mean-scale second derivative is `1 / 4 > 0`. -/
example : HasDerivAt (fun μ : ℝ => 1 * (0 - μ) / (μ * (1 + μ))) (1 / 4) 1 := by
  have h := hasDerivAt_nbKernelMean_deriv one_pos one_pos 0
  norm_num at h ⊢
  exact h

example : ¬ ConcaveOn ℝ (Set.Ioi 0) (nbKernelMean 1 0) := not_concaveOn_nbKernelMean_zero one_pos

/-! ### Intercept-only fixture: two observations, `y = (0, 2)`, `θ = 1`, `o = 0` -/

/-- The intercept-only design. -/
def X₀ : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of fun _ _ => 1

/-- The responses `(0, 2)`. -/
def y₀ : Fin 2 → ℝ := ![0, 2]

theorem X₀_mulVec (v : Fin 1 → ℝ) : X₀ *ᵥ v = fun _ => v 0 := by
  funext i
  simp [X₀, mulVec, dotProduct]

/-- At `β = 0` the two scores are `-1 / 2` and `1 / 2`, so the gradient vanishes. -/
example : nbGradient 1 X₀ 0 y₀ 0 = 0 := by
  funext j
  rw [nbGradient_apply]
  norm_num [Fin.sum_univ_two, nbScore, X₀, y₀]

/-- The Hessian quadratic form at `β = 0` along `u = 1`: weights `1 / 4` and `3 / 4`, total `-1`. -/
example :
    HasDerivAt (fun t : ℝ => nbGradient 1 X₀ 0 y₀ (0 + t • fun _ => 1) ⬝ᵥ fun _ => 1) (-1) 0 := by
  have h := hasDerivAt_nbGradient_dotProduct one_pos X₀ 0 y₀ 0 fun _ => 1
  have hw : ∑ i, nbObsWeight 1 (y₀ i) ((X₀ *ᵥ 0) i + (0 : Fin 2 → ℝ) i) *
      (X₀ *ᵥ fun _ => (1 : ℝ)) i ^ 2 = 1 := by
    norm_num [Fin.sum_univ_two, nbObsWeight, X₀_mulVec, y₀]
  rwa [hw] at h

/-- The zero gradient at `β = 0` is the Euclidean gradient of the log-likelihood there. -/
example : HasGradientAt (fun b : EuclideanSpace ℝ (Fin 1) => nbLogLik 1 X₀ 0 y₀ b.ofLp)
    (WithLp.toLp 2 (nbGradient 1 X₀ 0 y₀ 0)) (WithLp.toLp 2 0) :=
  hasGradientAt_nbLogLik one_pos X₀ 0 y₀ 0

example : ConcaveOn ℝ Set.univ (nbLogLik 1 X₀ 0 y₀) :=
  concaveOn_nbLogLik one_pos X₀ 0 fun i => by fin_cases i <;> norm_num [y₀]

/-- The Gram matrix `X₀ᵀ X₀ = (2)` is invertible. -/
theorem isUnit_gram_X₀ : IsUnit (X₀ᵀ * X₀) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_unique, isUnit_iff_ne_zero]
  norm_num [X₀, mul_apply, Fin.sum_univ_two]

example {β₁ β₂ : Fin 1 → ℝ} (h₁ : IsMaxOn (nbLogLik 1 X₀ 0 y₀) Set.univ β₁)
    (h₂ : IsMaxOn (nbLogLik 1 X₀ 0 y₀) Set.univ β₂) : β₁ = β₂ :=
  nbLogLik_maximizer_unique one_pos (mulVec_injective_of_isUnit_gram isUnit_gram_X₀) 0
    (fun i => by fin_cases i <;> norm_num [y₀]) h₁ h₂

/-! ### All-zero counts -/

example : nbScore 1 0 0 = -(1 / 2) := by norm_num [nbScore]

example : nbScore 1 0 0 < 0 := nbScore_zero_neg one_pos 0

/-- With both counts zero the intercept score is negative everywhere and there is no maximizer. -/
example (β : Fin 1 → ℝ) : nbGradient 1 X₀ 0 0 β 0 < 0 :=
  nbGradient_zero_neg one_pos 0 (fun _ => by norm_num [X₀]) ⟨0, by norm_num [X₀]⟩ 0 β

example (β : Fin 1 → ℝ) : ¬ IsMaxOn (nbLogLik 1 X₀ 0 0) Set.univ β :=
  nbLogLik_zero_not_isMaxOn one_pos 0 (fun _ => by norm_num [X₀]) ⟨0, by norm_num [X₀]⟩ 0 β

end MathlibExtTest.Probability.Statistics.GLM.NegativeBinomial
