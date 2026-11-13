/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GLM.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

open Finset Real Matrix
open MathlibExt.Probability.Statistics.GLM

namespace MathlibExtTest.Probability.Statistics.GLM.Basic

/-! ### Two families -/

/-- The Gaussian family with unknown mean: `b θ = θ² / 2`, `μ = id`, `V = 1`, on all of `ℝ`. -/
noncomputable def gaussian : CanonicalExpFamily where
  natDomain := Set.univ
  isOpen_natDomain := isOpen_univ
  convex_natDomain := convex_univ
  support := Set.univ
  cumulant θ := θ ^ 2 / 2
  mean θ := θ
  variance _ := 1
  hasDerivAt_cumulant θ _ := by
    simpa using (hasDerivAt_pow 2 θ).div_const 2
  hasDerivAt_mean θ _ := hasDerivAt_id θ
  variance_nonneg _ _ := zero_le_one

/-- The exponential family `b θ = -log (-θ)` on `θ < 0` (exponential responses on `(0, ∞)` with
rate `-θ`): `μ θ = -θ⁻¹`, `V θ = (θ²)⁻¹`. Its natural-parameter domain is a proper subset of `ℝ`. -/
noncomputable def exponential : CanonicalExpFamily where
  natDomain := Set.Iio 0
  isOpen_natDomain := isOpen_Iio
  convex_natDomain := convex_Iio 0
  support := Set.Ioi 0
  cumulant θ := -Real.log (-θ)
  mean θ := -θ⁻¹
  variance θ := (θ ^ 2)⁻¹
  hasDerivAt_cumulant θ hθ := by
    have hθ' : θ ≠ 0 := (Set.mem_Iio.1 hθ).ne
    have h := ((hasDerivAt_neg θ).log (neg_ne_zero.2 hθ')).neg
    convert h using 1
    field_simp
  hasDerivAt_mean θ hθ := by
    have hθ' : θ ≠ 0 := (Set.mem_Iio.1 hθ).ne
    have h := (hasDerivAt_inv hθ').fun_neg
    rwa [neg_neg] at h
  variance_nonneg θ _ := inv_nonneg.2 (sq_nonneg θ)

theorem gaussian_variance_pos : ∀ θ ∈ gaussian.natDomain, 0 < gaussian.variance θ :=
  fun _ _ => zero_lt_one

theorem exponential_variance_pos :
    ∀ θ ∈ exponential.natDomain, 0 < exponential.variance θ :=
  fun θ hθ => inv_pos.2 (by nlinarith [(show θ < 0 from hθ)])

/-! ### A full-rank design: 2 observations, 1 covariate, Gaussian, `φ = 2` -/

/-- Covariate `x = (1, 2)`, no intercept. -/
noncomputable def X₁ : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of ![![1], ![2]]

/-- Fixed offset `o = (0, 1)`. -/
noncomputable def o₁ : Fin 2 → ℝ := ![0, 1]

/-- Responses `y = (1, 3)`. -/
noncomputable def y₁ : Fin 2 → ℝ := ![1, 3]

theorem X₁_mulVec_injective : Function.Injective X₁.mulVec := by
  intro β γ h
  have h0 := congrFun h 0
  simp [X₁, Matrix.mulVec, dotProduct] at h0
  funext k
  fin_cases k
  exact h0

theorem glmPredictor_X₁ (β : Fin 1 → ℝ) :
    glmPredictor X₁ o₁ β = ![β 0, 2 * β 0 + 1] := by
  funext i
  fin_cases i <;> simp [glmPredictor, X₁, o₁, dotProduct]

/-- The log likelihood from the definition: `ℓ(b) = (5 b - 5 b² / 2 + 5 / 2) / 2`. -/
theorem glmLogLik_X₁ (β : Fin 1 → ℝ) :
    gaussian.glmLogLik 2 X₁ o₁ y₁ β = (5 * β 0 - 5 / 2 * β 0 ^ 2 + 5 / 2) / 2 := by
  simp only [CanonicalExpFamily.glmLogLik, glmPredictor_X₁, Fin.sum_univ_two, gaussian, y₁]
  simp
  ring

/-- The score from the definition: `Xᵀ (y - η) / 2 = (5 - 5 b) / 2`. -/
theorem glmScore_X₁ (β : Fin 1 → ℝ) :
    gaussian.glmScore 2 X₁ o₁ y₁ β = fun _ => (5 - 5 * β 0) / 2 := by
  funext k
  fin_cases k
  simp only [CanonicalExpFamily.glmScore, glmPredictor_X₁]
  simp [gaussian, X₁, y₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The Hessian from the definition: `-Xᵀ X / 2 = -(1 + 4) / 2`, the same at every `β`. -/
theorem glmHessian_X₁ (β : Fin 1 → ℝ) : gaussian.glmHessian 2 X₁ o₁ β = !![-5 / 2] := by
  ext i j
  fin_cases i
  fin_cases j
  simp [CanonicalExpFamily.glmHessian, CanonicalExpFamily.glmWeights, IRLS.weightedGram,
    gaussian, X₁, Matrix.mul_apply, Fin.sum_univ_two]
  norm_num

/-- The score vanishes exactly at `b = 1`. -/
theorem glmScore_X₁_eq_zero_iff (β : Fin 1 → ℝ) :
    gaussian.glmScore 2 X₁ o₁ y₁ β = 0 ↔ β 0 = 1 := by
  rw [glmScore_X₁]
  constructor
  · intro h
    have := congrFun h 0
    simp only [Pi.zero_apply] at this
    linarith
  · intro h
    funext k
    simp [h]

/-- Concavity read off the definition: the midpoint of `b = 0` and `b = 2` has a larger log
likelihood (`5 / 2`) than the average of the endpoints (`5 / 4`). -/
theorem glmLogLik_X₁_midpoint :
    (1 / 2 : ℝ) * gaussian.glmLogLik 2 X₁ o₁ y₁ ![0] +
        1 / 2 * gaussian.glmLogLik 2 X₁ o₁ y₁ ![2] <
      gaussian.glmLogLik 2 X₁ o₁ y₁ ![1] := by
  rw [glmLogLik_X₁, glmLogLik_X₁, glmLogLik_X₁]
  norm_num

/-- The general concavity theorem applies to this design. -/
theorem concaveOn_glmLogLik_X₁ :
    ConcaveOn ℝ (gaussian.glmDomain X₁ o₁) (gaussian.glmLogLik 2 X₁ o₁ y₁) :=
  gaussian.concaveOn_glmLogLik two_pos X₁ o₁ y₁

/-- The Hessian quadratic form from the definition is `-(5 / 2) u²`. -/
theorem glmHessian_X₁_quadForm (β u : Fin 1 → ℝ) :
    u ⬝ᵥ (gaussian.glmHessian 2 X₁ o₁ β *ᵥ u) = -(5 / 2) * u 0 ^ 2 := by
  rw [glmHessian_X₁]
  simp [Matrix.mulVec, dotProduct]
  ring

theorem glmDomain_gaussian (X : Matrix (Fin 2) (Fin 1) ℝ) (o : Fin 2 → ℝ) (β : Fin 1 → ℝ) :
    β ∈ gaussian.glmDomain X o :=
  fun _ => Set.mem_univ _

/-- `b = 1` maximizes the log likelihood, computed from `ℓ(b) = 5 / 2 - 5 (b - 1)² / 4`. -/
theorem isMaxOn_glmLogLik_X₁ :
    IsMaxOn (gaussian.glmLogLik 2 X₁ o₁ y₁) (gaussian.glmDomain X₁ o₁) ![1] := by
  intro β _
  simp only [Set.mem_ofPred_eq, glmLogLik_X₁]
  simp only [Matrix.cons_val_zero]
  nlinarith [sq_nonneg (β 0 - 1)]

/-- Non-vacuity of `glmLogLik_maximizer_unique`: its hypotheses hold for this design, and every
maximizer in the domain is `b = 1`. -/
theorem glmLogLik_X₁_maximizer_eq {β : Fin 1 → ℝ}
    (h : IsMaxOn (gaussian.glmLogLik 2 X₁ o₁ y₁) (gaussian.glmDomain X₁ o₁) β) : β = ![1] :=
  gaussian.glmLogLik_maximizer_unique two_pos X₁_mulVec_injective gaussian_variance_pos o₁ y₁
    (glmDomain_gaussian _ _ _) (glmDomain_gaussian _ _ _) h isMaxOn_glmLogLik_X₁

/-! ### A rank-deficient design: at-most-one fails -/

/-- Two identical columns: `X₂ = [[1, 1], [1, 1]]`. -/
noncomputable def X₂ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of ![![1, 1], ![1, 1]]

theorem X₂_mulVec_not_injective : ¬ Function.Injective X₂.mulVec := by
  intro h
  have e : X₂ *ᵥ ![1, 0] = X₂ *ᵥ ![0, 1] := by
    funext i
    fin_cases i <;> simp [X₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have := congrFun (h e) 0
  simp at this

/-- With `y = (1, 1)`, zero offset and `φ = 1`, the Gaussian log likelihood depends only on
`s = b₀ + b₁`: `ℓ(b) = 1 - (s - 1)²`. -/
theorem glmLogLik_X₂ (β : Fin 2 → ℝ) :
    gaussian.glmLogLik 1 X₂ 0 ![1, 1] β = 1 - (β 0 + β 1 - 1) ^ 2 := by
  simp [CanonicalExpFamily.glmLogLik, glmPredictor, gaussian, X₂, dotProduct, Fin.sum_univ_two]
  ring

theorem isMaxOn_glmLogLik_X₂ (β : Fin 2 → ℝ) (hβ : β 0 + β 1 = 1) :
    IsMaxOn (gaussian.glmLogLik 1 X₂ 0 ![1, 1]) (gaussian.glmDomain X₂ 0) β := by
  intro γ _
  simp only [Set.mem_ofPred_eq, glmLogLik_X₂, hβ]
  nlinarith [sq_nonneg (γ 0 + γ 1 - 1)]

/-- Without full rank there are two distinct maximizers, `(1, 0)` and `(0, 1)`, so the full-rank
hypothesis of `glmLogLik_maximizer_unique` cannot be dropped (weights are still positive). -/
theorem glmLogLik_X₂_two_maximizers :
    ∃ β₁ β₂ : Fin 2 → ℝ, β₁ ≠ β₂ ∧
      IsMaxOn (gaussian.glmLogLik 1 X₂ 0 ![1, 1]) (gaussian.glmDomain X₂ 0) β₁ ∧
      IsMaxOn (gaussian.glmLogLik 1 X₂ 0 ![1, 1]) (gaussian.glmDomain X₂ 0) β₂ := by
  refine ⟨![1, 0], ![0, 1], fun h => by simpa using congrFun h 0,
    isMaxOn_glmLogLik_X₂ _ (by simp), isMaxOn_glmLogLik_X₂ _ (by simp)⟩

/-! ### A restricted natural-parameter domain with a fixed offset -/

/-- For the exponential family (`θ < 0`) with design `X₁` and offset `o₁ = (0, 1)`, the
coefficient domain is `b < -1 / 2`: the offset moves the boundary. -/
theorem mem_glmDomain_exponential_iff (β : Fin 1 → ℝ) :
    β ∈ exponential.glmDomain X₁ o₁ ↔ β 0 < -1 / 2 := by
  simp only [CanonicalExpFamily.glmDomain, Set.mem_ofPred_eq, glmPredictor_X₁, exponential,
    Fin.forall_fin_two, Set.mem_Iio, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨_, h⟩
    linarith
  · intro h
    constructor <;> linarith

theorem neg_quarter_not_mem_glmDomain_exponential : ![-1 / 4] ∉ exponential.glmDomain X₁ o₁ := by
  rw [mem_glmDomain_exponential_iff]
  norm_num

/-- The score of the exponential family from the definition: `Xᵀ (y + η⁻¹)` with `φ = 1`. -/
theorem glmScore_exponential_X₁ (β : Fin 1 → ℝ) :
    exponential.glmScore 1 X₁ o₁ y₁ β =
      fun _ => (1 + (β 0)⁻¹) + 2 * (3 + (2 * β 0 + 1)⁻¹) := by
  funext k
  fin_cases k
  simp only [CanonicalExpFamily.glmScore, glmPredictor_X₁]
  simp [exponential, X₁, y₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.vecHead,
    Matrix.vecTail]

/-- Non-vacuity on a restricted domain: the exponential-family log likelihood has at most one
maximizer on `b < -1 / 2`. -/
theorem glmLogLik_exponential_X₁_unique {β₁ β₂ : Fin 1 → ℝ}
    (hβ₁ : β₁ ∈ exponential.glmDomain X₁ o₁) (hβ₂ : β₂ ∈ exponential.glmDomain X₁ o₁)
    (h₁ : IsMaxOn (exponential.glmLogLik 1 X₁ o₁ y₁) (exponential.glmDomain X₁ o₁) β₁)
    (h₂ : IsMaxOn (exponential.glmLogLik 1 X₁ o₁ y₁) (exponential.glmDomain X₁ o₁) β₂) :
    β₁ = β₂ :=
  exponential.glmLogLik_maximizer_unique one_pos X₁_mulVec_injective exponential_variance_pos
    o₁ y₁ hβ₁ hβ₂ h₁ h₂

end MathlibExtTest.Probability.Statistics.GLM.Basic
