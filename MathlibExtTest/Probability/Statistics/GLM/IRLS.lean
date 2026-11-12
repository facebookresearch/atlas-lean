/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GLM.IRLS
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

open Matrix
open MathlibExt.Probability.Statistics.GLM.IRLS

namespace MathlibExtTest.Probability.Statistics.GLM.IRLS

/-! ### Gaussian family with identity link (`b(η) = η² / 2`, `mean = id`, `weight = 1`) -/

theorem irlsWeights_one {m k : Type*} [Fintype k] (X : Matrix m k ℝ) (β : k → ℝ) :
    irlsWeights (fun _ => 1) X β = 1 := rfl

theorem weightedGram_one {m k : Type*} [Fintype m] [DecidableEq m] (X : Matrix m k ℝ) :
    weightedGram X 1 = Xᵀ * X := by
  simp [weightedGram]

/-- The least-squares score `Xᵀ (y - X β)` and Hessian `-Xᵀ X` satisfy the canonical-link
hypotheses of the Gaussian family, so the bundle is not vacuous. -/
theorem gaussian_isCanonical {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    (X : Matrix m k ℝ) (y : m → ℝ) :
    IsCanonicalScoreHessian X y id (fun _ => 1) (fun β => Xᵀ *ᵥ (y - X *ᵥ β))
      (fun _ => -(Xᵀ * X)) where
  score_eq _ := rfl
  hess_eq β := by rw [irlsWeights_one, weightedGram_one]

/-- For the Gaussian family the working response at `β` is `y` itself. -/
example {m k : Type*} [Fintype k] (X : Matrix m k ℝ) (y : m → ℝ) (β : k → ℝ) :
    workingResponse X y id (fun _ => 1) β = y := by
  funext i
  simp [workingResponse]

/-- The one-observation Gaussian model `y = 3`, `X = 1`: from `β = 0`, one IRLS step lands on the
least-squares fit `3`. -/
example :
    irlsStep (1 : Matrix (Fin 1) (Fin 1) ℝ) ![3] id (fun _ => 1) ![0] = ![3] := by
  rw [irlsStep_eq _ (fun _ => one_ne_zero) (by rw [irlsWeights_one, weightedGram_one]; simp)]
  rw [irlsWeights_one, weightedGram_one]
  funext i
  fin_cases i
  simp

/-- The Gaussian Newton step equals the IRLS step (`newtonStep_eq_irlsStep`). -/
example (β : Fin 1 → ℝ) :
    newtonStep (fun β => (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ *ᵥ (![3] - 1 *ᵥ β))
        (fun _ => -((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 1)) β =
      irlsStep 1 ![3] id (fun _ => 1) β :=
  newtonStep_eq_irlsStep (gaussian_isCanonical 1 ![3]) β (fun _ => one_ne_zero)
    (by rw [irlsWeights_one, weightedGram_one]; simp)

/-- The least-squares fit `β = 3` is an IRLS fixed point, and the score vanishes there. -/
example : irlsStep (1 : Matrix (Fin 1) (Fin 1) ℝ) ![3] id (fun _ => 1) ![3] = ![3] := by
  rw [irlsStep_eq_self_iff _ (fun _ => one_ne_zero)
    (by rw [irlsWeights_one, weightedGram_one]; simp)]
  funext i
  fin_cases i
  simp

/-- `β = 0` is not an IRLS fixed point because the score `3` does not vanish there. -/
example : irlsStep (1 : Matrix (Fin 1) (Fin 1) ℝ) ![3] id (fun _ => 1) ![0] ≠ ![0] := by
  rw [Ne, irlsStep_eq_self_iff_score_eq_zero (gaussian_isCanonical 1 ![3]) _
    (fun _ => one_ne_zero) (by rw [irlsWeights_one, weightedGram_one]; simp)]
  intro h
  have := congrFun h 0
  simp at this

/-- The IRLS iteration reaches the least-squares fit after one step and stays there. -/
example (n : ℕ) :
    irlsIterate (1 : Matrix (Fin 1) (Fin 1) ℝ) ![3] id (fun _ => 1) ![3] n = ![3] := by
  have hfix : irlsStep (1 : Matrix (Fin 1) (Fin 1) ℝ) ![3] id (fun _ => 1) ![3] = ![3] := by
    rw [irlsStep_eq_self_iff _ (fun _ => one_ne_zero)
      (by rw [irlsWeights_one, weightedGram_one]; simp)]
    funext i
    fin_cases i
    simp
  exact Function.iterate_fixed hfix n

/-- Newton–Raphson iterates agree with IRLS iterates for the Gaussian model. -/
example (β₀ : Fin 1 → ℝ) (n : ℕ) :
    (newtonStep (fun β => (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ *ᵥ (![3] - 1 *ᵥ β))
        (fun _ => -((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 1)))^[n] β₀ =
      irlsIterate 1 ![3] id (fun _ => 1) β₀ n :=
  newtonIterate_eq_irlsIterate (gaussian_isCanonical 1 ![3]) (fun _ _ => one_ne_zero)
    (fun _ => by rw [irlsWeights_one, weightedGram_one]; simp) β₀ n

/-! ### Weighted least squares -/

/-- With unit weights the WLS estimate solves the ordinary normal equations. -/
example : (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ *ᵥ
    ((1 : Fin 1 → ℝ) * (![3] - 1 *ᵥ wlsEstimate (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 ![3])) = 0 :=
  normal_eq_wlsEstimate (fun _ => one_ne_zero) (by simp [weightedGram]) ![3]

/-- The WLS estimate has weighted residual sum of squares no larger than at `b = 0`. -/
example : wrss (1 : Matrix (Fin 1) (Fin 1) ℝ) ![2] ![3] (wlsEstimate 1 ![2] ![3]) ≤
    wrss 1 ![2] ![3] ![0] :=
  wrss_wlsEstimate_le (fun i => by fin_cases i; norm_num) (fun i => by fin_cases i; norm_num)
    ((isUnit_iff_isUnit_det _).mpr (by simp [weightedGram])) ![3] ![0]

/-- The weighted residual sum of squares of `z = 3`, `w = 2` at `b = 0` is `2 · 3² = 18`. -/
example : wrss (1 : Matrix (Fin 1) (Fin 1) ℝ) ![2] ![3] ![0] = 18 := by
  norm_num [wrss]

/-- Two observations with unequal weights: the WLS estimate is the weighted mean
`(1 · 0 + 3 · 4) / (1 + 3) = 3`. Using `w⁻¹` in place of `w` would give `1`, so this example
detects a weight/covariance flip. -/
example : wlsEstimate (!![1; 1] : Matrix (Fin 2) (Fin 1) ℝ) ![1, 3] ![0, 4] = ![3] := by
  rw [wlsEstimate_eq (fun i => by fin_cases i <;> norm_num)]
  funext i
  fin_cases i
  simp [weightedGram, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]
  norm_num

/-! ### Boundary: a singular weighted Gram matrix -/

/-- The invertibility hypothesis cannot be dropped from `irlsStep_eq_self_iff`: for
`X = [1 1]` the Gram matrix `Xᵀ X` is singular, `β = 0` is an IRLS fixed point, yet the score
`Xᵀ (5 - 0)` is nonzero. -/
example : irlsStep (!![1, 1] : Matrix (Fin 1) (Fin 2) ℝ) ![5] id (fun _ => 1) 0 = 0 ∧
    (!![1, 1] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ *ᵥ
      (![5] - fun i => id ((!![1, 1] : Matrix (Fin 1) (Fin 2) ℝ) *ᵥ 0) i) ≠ 0 := by
  constructor
  · simp [irlsStep, wlsEstimate,
      MathlibExt.Probability.Statistics.GeneralizedLeastSquares.glsMatrix,
      Matrix.inv_def, Matrix.det_fin_two, Matrix.mul_apply]
  · intro h
    have := congrFun h 0
    simp [Matrix.mulVec, dotProduct] at this

/-- Conversely, for `X = 0` the score vanishes at `β = 1` but `β = 1` is not an IRLS fixed
point. -/
example : (0 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ *ᵥ
      (![5] - fun i => id ((0 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ ![1]) i) = 0 ∧
    irlsStep (0 : Matrix (Fin 1) (Fin 1) ℝ) ![5] id (fun _ => 1) ![1] ≠ ![1] := by
  refine ⟨by simp, ?_⟩
  intro h
  have := congrFun h 0
  simp [irlsStep, wlsEstimate,
    MathlibExt.Probability.Statistics.GeneralizedLeastSquares.glsMatrix] at this

/-- The Gaussian Hessian `-Xᵀ X` is the derivative of the least-squares score, via
`IsCanonicalScoreHessian.hasFDerivAt`. -/
example {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
    (X : Matrix m k ℝ) (y : m → ℝ) (β : k → ℝ) :
    HasFDerivAt (fun β => Xᵀ *ᵥ (y - X *ᵥ β))
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (-(Xᵀ * X)))) β :=
  (gaussian_isCanonical X y).hasFDerivAt (fun x => hasDerivAt_id x) β

/-! ### Poisson family with log link (`b = exp`, `mean = weight = exp`) -/

/-- For Poisson regression with its canonical log link, the score `Xᵀ (y - exp (X β))` has
derivative `-Xᵀ diag(exp (X β)) X`. -/
example {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
    (X : Matrix m k ℝ) (y : m → ℝ) (β : k → ℝ) :
    HasFDerivAt (fun β' => Xᵀ *ᵥ (y - fun i => Real.exp ((X *ᵥ β') i)))
      (LinearMap.toContinuousLinearMap
        (Matrix.toLin' (-weightedGram X (irlsWeights Real.exp X β)))) β :=
  hasFDerivAt_canonicalScore β fun _ => Real.hasDerivAt_exp _

/-- Poisson IRLS weights `exp ηᵢ` are positive, so the nonzero-weight hypothesis always holds. -/
example {m k : Type*} [Fintype k] (X : Matrix m k ℝ) (β : k → ℝ) (i : m) :
    irlsWeights Real.exp X β i ≠ 0 :=
  (Real.exp_pos _).ne'

end MathlibExtTest.Probability.Statistics.GLM.IRLS
