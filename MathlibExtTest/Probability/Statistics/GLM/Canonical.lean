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
example : glmPredictor X₀ ![1, 2] ![3, 4] = ![4, 9] := by
  ext i
  fin_cases i <;> simp [glmPredictor_apply, X₀, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    norm_num

/-- The per-observation identity at `y = 1 / 2` (non-binary responses are allowed). -/
example (η : ℝ) :
    (1 / 2) * log (sigmoid η) + (1 - 1 / 2) * log (1 - sigmoid η) =
      (1 / 2) * η - log (1 + exp η) :=
  sigmoid_logLik_term _ _

/-- Logistic score at `β = 0`, `y = (1, 0)`: `μ = (1/2, 1/2)`, `Xᵀ (y - μ) = (0, -1/2)`. -/
example : HasFDerivAt (logisticLogLik X₀ 0 ![1, 0]) (Real.dotL ![0, -1 / 2]) 0 := by
  have e : (![0, -1 / 2] : Fin 2 → ℝ) =
      X₀.transpose *ᵥ (![1, 0] - sigmoid ∘ glmPredictor X₀ 0 0) := by
    ext j
    fin_cases j <;>
      simp [X₀, glmPredictor_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  rw [e]
  exact hasFDerivAt_logisticLogLik X₀ 0 ![1, 0] 0

/-- Poisson score at `β = 0`, `y = (2, 0)`: `exp η = (1, 1)`, `Xᵀ (y - exp η) = (0, -1)`. -/
example : HasFDerivAt (poissonLogLikKernel X₀ 0 ![2, 0]) (Real.dotL ![0, -1]) 0 := by
  have e : (![0, -1] : Fin 2 → ℝ) =
      X₀.transpose *ᵥ (![2, 0] - exp ∘ glmPredictor X₀ 0 0) := by
    ext j
    fin_cases j <;>
      simp [X₀, glmPredictor_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    norm_num
  rw [e]
  exact hasFDerivAt_poissonLogLikKernel X₀ 0 ![2, 0] 0

/-- Logistic curvature at `β = 0` along the covariate direction: `-(1/4) · 1`. -/
example : deriv^[2] (fun t : ℝ => logisticLogLik X₀ 0 ![1, 0] (0 + t • ![0, 1])) 0 = -1 / 4 := by
  rw [deriv2_logisticLogLik_line]
  simp [X₀, glmPredictor_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  norm_num

/-- Poisson curvature at `β = 0` along the covariate direction: `-exp 0 · 1`. -/
example : deriv^[2] (fun t : ℝ => poissonLogLikKernel X₀ 0 ![2, 0] (0 + t • ![0, 1])) 0 = -1 := by
  rw [deriv2_poissonLogLikKernel_line]
  simp [X₀, glmPredictor_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

example : ConcaveOn ℝ Set.univ (logisticLogLik X₀ 0 ![1, 0]) := concaveOn_logisticLogLik _ _ _

example : ConcaveOn ℝ Set.univ (poissonLogLikKernel X₀ 0 ![2, 0]) :=
  concaveOn_poissonLogLikKernel _ _ _

/-- Uniqueness applied to the full-rank fixture. -/
example {β₁ β₂ : Fin 2 → ℝ} (h₁ : IsMaxOn (logisticLogLik X₀ 0 ![1, 0]) Set.univ β₁)
    (h₂ : IsMaxOn (logisticLogLik X₀ 0 ![1, 0]) Set.univ β₂) : β₁ = β₂ :=
  logisticLogLik_maximizer_unique X₀ 0 _ X₀_mulVec_injective h₁ h₂

example {β₁ β₂ : Fin 2 → ℝ} (h₁ : IsMaxOn (poissonLogLikKernel X₀ 0 ![2, 0]) Set.univ β₁)
    (h₂ : IsMaxOn (poissonLogLikKernel X₀ 0 ![2, 0]) Set.univ β₂) : β₁ = β₂ :=
  poissonLogLikKernel_maximizer_unique X₀ 0 _ X₀_mulVec_injective h₁ h₂

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
    ¬ IsMaxOn (poissonLogLikKernel (Matrix.of fun (_ : Fin 3) (_ : Fin 1) => (1 : ℝ)) 0 0)
      Set.univ β :=
  poissonLogLikKernel_allZero_not_isMaxOn β

example : poissonLogLikKernel (Matrix.of fun (_ : Fin 3) (_ : Fin 1) => (1 : ℝ)) 0 0 0 = -3 := by
  rw [poissonLogLikKernel_allZero]
  simp

/-- The count likelihood at `β = 0` with counts `(2, 0)`: both means are `1`, so
`ℓ = (2 · 0 - 1 - log 2!) + (0 · 0 - 1 - log 0!) = -2 - log 2`. -/
example : poissonLogLik X₀ 0 ![2, 0] 0 = -2 - log 2 := by
  rw [poissonLogLik_eq_kernel]
  simp [poissonLogLikKernel_eq_sum, glmPredictor_apply, Fin.sum_univ_two, Nat.factorial_two]

/-- The same value is the log-probability of the counts `(2, 0)` under the joint law of
independent `Poisson(exp ηᵢ)` responses at `β = 0`. -/
example : log ((MeasureTheory.Measure.pi fun i => ProbabilityTheory.poissonMeasure
      ⟨exp (glmPredictor X₀ 0 0 i), (exp_pos _).le⟩).real {![2, 0]}) = -2 - log 2 := by
  rw [← poissonLogLik_eq_log_pi_poissonMeasure, poissonLogLik_eq_kernel]
  simp [poissonLogLikKernel_eq_sum, glmPredictor_apply, Fin.sum_univ_two, Nat.factorial_two]

/-- Uniqueness transfers from the kernel to the count likelihood. -/
example {β₁ β₂ : Fin 2 → ℝ} (h₁ : IsMaxOn (poissonLogLik X₀ 0 ![2, 0]) Set.univ β₁)
    (h₂ : IsMaxOn (poissonLogLik X₀ 0 ![2, 0]) Set.univ β₂) : β₁ = β₂ :=
  poissonLogLikKernel_maximizer_unique X₀ 0 _ X₀_mulVec_injective
    ((isMaxOn_poissonLogLik_iff _ _ _).1 h₁) ((isMaxOn_poissonLogLik_iff _ _ _).1 h₂)

/-- All-zero counts: the count likelihood has no maximizer either. -/
example (β : Fin 1 → ℝ) :
    ¬ IsMaxOn (poissonLogLik (Matrix.of fun (_ : Fin 3) (_ : Fin 1) => (1 : ℝ)) 0 0)
      Set.univ β := by
  have e : (fun i => ((0 : Fin 3 → ℕ) i : ℝ)) = 0 := by
    ext
    simp
  rw [isMaxOn_poissonLogLik_iff, e]
  exact poissonLogLikKernel_allZero_not_isMaxOn β

/-- The saturated term is not identically zero: `-H(1/2) = -log 2`. -/
example : logisticLogLikSaturated (![2⁻¹] : Fin 1 → ℝ) = -log 2 := by
  simp [logisticLogLikSaturated]

example : logisticLogLikSaturated (![1, 0] : Fin 2 → ℝ) = 0 :=
  logisticLogLikSaturated_eq_zero _ fun i => by fin_cases i <;> simp

/-- Deviance at `β = 0` for `y = (1, 0)`: `ℓ(0) = -2 log 2`, so `D = 4 log 2 > 0`. -/
example : logisticDeviance X₀ 0 ![1, 0] 0 = 4 * log 2 := by
  rw [logisticDeviance_eq X₀ 0 _ fun i => by fin_cases i <;> simp]
  simp [logisticLogLik_eq_sum, glmPredictor_apply]
  norm_num [one_add_one_eq_two]
  ring

example (β : Fin 2 → ℝ) : 0 ≤ logisticDeviance X₀ 0 ![1, 0] β :=
  logisticDeviance_nonneg X₀ 0 _ (fun i => by fin_cases i <;> simp) β

example (η : ℝ) : 1 * η - log (1 + exp η) < 0 := logisticTerm_neg (Or.inr rfl) η

/-- Outside `[0, 1]` the saturated formula is only an algebraic extension: `y = 2` gives
`2 log 2 > 0`, which is not a log probability. -/
theorem logisticLogLikSaturated_two : logisticLogLikSaturated (![2] : Fin 1 → ℝ) = 2 * log 2 := by
  rw [logisticLogLikSaturated_eq]
  norm_num [Real.log_neg_eq_log]

/-- Outside `[0, 1]` the deviance formula can be negative: `y = 2`, `η = log 7` gives
`2 (2 log 2 - (2 log 7 - log 8)) = 10 log 2 - 4 log 7 < 0`. -/
example :
    logisticDeviance (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => (1 : ℝ)) 0 ![2] ![log 7] < 0 := by
  have h7 : exp (log 7) = 7 := exp_log (by norm_num)
  have h8 : log (1 + 7 : ℝ) = 3 * log 2 := by
    rw [show (1 + 7 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast
    ring
  have hlt : log ((2 : ℝ) ^ 10) < log ((7 : ℝ) ^ 4) := Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at hlt
  push_cast at hlt
  simp only [logisticDeviance, logisticLogLikSaturated_two, logisticLogLik_eq_sum,
    glmPredictor_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_one, Matrix.of_apply,
    Matrix.cons_val_zero, one_mul, Pi.zero_apply, add_zero, h7, h8]
  linarith

/-! ### The objectives are the generic `CanonicalCumulant` instances -/

/-- The logistic log likelihood is the generic canonical-link log likelihood of
`logisticCumulant` at unit dispersion. -/
example : logisticLogLik X₀ 0 ![1, 0] = logisticCumulant.glmLogLik unitDispersion X₀ 0 ![1, 0] :=
  rfl

/-- The Poisson kernel is the generic canonical-link log likelihood of `poissonCumulant` at unit
dispersion. -/
example :
    poissonLogLikKernel X₀ 0 ![2, 0] = poissonCumulant.glmLogLik unitDispersion X₀ 0 ![2, 0] :=
  rfl

/-- Logistic instance score, computed by unfolding the generic `glmScore` and the instance at
`β = 0`, `y = (1, 0)`: the old value `Xᵀ (y - μ) = (0, -1/2)`. -/
example : logisticCumulant.glmScore unitDispersion X₀ 0 ![1, 0] 0 = ![0, -1 / 2] := by
  ext j
  fin_cases j <;>
    simp [CanonicalCumulant.glmScore, logisticCumulant, X₀, glmPredictor_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail] <;> norm_num

/-- Logistic instance Hessian, computed by unfolding the generic `glmHessian` and the instance at
`β = 0`: weights `σ(0)(1 - σ(0)) = 1/4`, so `H = -(1/4) Xᵀ X`. -/
example :
    logisticCumulant.glmHessian unitDispersion X₀ 0 0 = !![-1 / 2, -1 / 4; -1 / 4, -1 / 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CanonicalCumulant.glmHessian, CanonicalCumulant.glmWeights, logisticCumulant,
      IRLS.weightedGram, X₀, glmPredictor_apply, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- The instance Hessian's quadratic form along the covariate direction is the old curvature
`-1/4` of `deriv2_logisticLogLik_line`. -/
example :
    ![0, 1] ⬝ᵥ (logisticCumulant.glmHessian unitDispersion X₀ 0 0 *ᵥ ![0, 1]) = -1 / 4 := by
  rw [CanonicalCumulant.dotProduct_glmHessian_mulVec]
  simp [CanonicalCumulant.glmWeights, logisticCumulant, X₀, glmPredictor_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]
  norm_num

/-- Poisson instance score, computed by unfolding the generic `glmScore` and the instance at
`β = 0`, `y = (2, 0)`: the old value `Xᵀ (y - exp η) = (0, -1)`. -/
example : poissonCumulant.glmScore unitDispersion X₀ 0 ![2, 0] 0 = ![0, -1] := by
  ext j
  fin_cases j <;>
    simp [CanonicalCumulant.glmScore, poissonCumulant, X₀, glmPredictor_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail]
  norm_num

/-- Poisson instance Hessian, computed by unfolding the generic `glmHessian` and the instance at
`β = 0`: weights `exp 0 = 1`, so `H = -Xᵀ X`. -/
example : poissonCumulant.glmHessian unitDispersion X₀ 0 0 = !![-2, -1; -1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CanonicalCumulant.glmHessian, CanonicalCumulant.glmWeights, poissonCumulant,
      IRLS.weightedGram, X₀, glmPredictor_apply, Matrix.mul_apply, Fin.sum_univ_two]
  norm_num

/-- The Poisson instance Hessian's quadratic form along the covariate direction is the old
curvature `-1` of `deriv2_poissonLogLikKernel_line`. -/
example : ![0, 1] ⬝ᵥ (poissonCumulant.glmHessian unitDispersion X₀ 0 0 *ᵥ ![0, 1]) = -1 := by
  rw [CanonicalCumulant.dotProduct_glmHessian_mulVec]
  simp [CanonicalCumulant.glmWeights, poissonCumulant, X₀, glmPredictor_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]

/-- The specialized score theorem agrees with the generic instance score. -/
example : logisticCumulant.glmScore unitDispersion X₀ 0 ![1, 0] 0 =
    X₀.transpose *ᵥ (![1, 0] - sigmoid ∘ glmPredictor X₀ 0 0) :=
  logisticCumulant_glmScore _ _ _ _

/-- Deviance at `β = 0` for `y = (1, 0)` through the instance: `2 (0 - ℓ(0)) = 4 log 2`. -/
example : 2 * (logisticLogLikSaturated ![1, 0] -
    logisticCumulant.glmLogLik unitDispersion X₀ 0 ![1, 0] 0) = 4 * log 2 := by
  rw [logisticLogLikSaturated_eq_zero _ fun i => by fin_cases i <;> simp]
  simp [CanonicalCumulant.glmLogLik, logisticCumulant, glmPredictor_apply]
  norm_num [one_add_one_eq_two]
  ring

/-! ### Bernoulli family structure: sufficient statistic `y`, log-partition `log (1 + exp θ)` -/

/-- With sufficient statistic `T(y) = y` and log-partition `b`, the densities `exp (y θ - b θ)`
over `y ∈ {0, 1}` sum to one, computed from the instance's cumulant. -/
example (θ : ℝ) :
    ∑ y ∈ ({0, 1} : Finset ℝ), exp (y * θ - logisticCumulant.cumulant θ) = 1 := by
  have h : (0 : ℝ) < 1 + exp θ := by positivity
  rw [Finset.sum_pair zero_ne_one]
  simp only [logisticCumulant, zero_mul, one_mul, zero_sub, exp_neg, exp_sub, exp_log h]
  field_simp

/-- The mean of the sufficient statistic, `∑_{y ∈ {0, 1}} y exp (y θ - b θ)`, is the instance's
mean function `σ θ`, computed from the definitions. -/
example (θ : ℝ) :
    ∑ y ∈ ({0, 1} : Finset ℝ), y * exp (y * θ - logisticCumulant.cumulant θ) =
      logisticCumulant.mean θ := by
  have h : (0 : ℝ) < 1 + exp θ := by positivity
  rw [Finset.sum_pair zero_ne_one]
  simp only [logisticCumulant, zero_mul, one_mul, zero_add, exp_sub, exp_log h, sigmoid_def,
    exp_neg]
  field_simp
  ring

/-- At `θ = 0` the success probability is `1/2`, from the definitions. -/
example : exp (1 * 0 - logisticCumulant.cumulant 0) = 1 / 2 := by
  simp [logisticCumulant, one_add_one_eq_two, exp_neg, exp_log]

example (θ : ℝ) : exp (1 * θ - logisticCumulant.cumulant θ) = sigmoid θ :=
  exp_logisticCumulant_one θ

example (θ : ℝ) : exp (0 * θ - logisticCumulant.cumulant θ) = 1 - sigmoid θ :=
  exp_logisticCumulant_zero θ

/-- The library log-partition identity at `θ = 0`: `log 2`. -/
example : log (∑ y ∈ ({0, 1} : Finset ℝ), exp (y * 0)) = log 2 := by
  rw [← logisticCumulant_cumulant_eq_log_sum_exp]
  simp [one_add_one_eq_two]

/-- Poisson: `P(Y = 0) = exp (-1)` for `Y ~ Poisson(exp 0)`. -/
example : (ProbabilityTheory.poissonMeasure ⟨exp 0, (exp_pos 0).le⟩).real {0} = exp (-1) := by
  rw [poissonMeasure_real_singleton_eq_exp]
  simp

end MathlibExtTest.Probability.Statistics.GLM
