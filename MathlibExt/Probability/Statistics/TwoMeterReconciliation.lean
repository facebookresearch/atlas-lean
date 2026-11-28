/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GeneralizedLeastSquares
public import Mathlib.Probability.Moments.Variance

import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Weighted reconciliation of two meters -/

open Matrix MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.Statistics.GeneralizedLeastSquares

private theorem twoMeter_gls_data {v₁ v₂ : ℝ} (h₁ : 0 < v₁) (h₂ : 0 < v₂) :
    let X : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of fun _ _ => 1
    let V : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![v₁, v₂]
    IsUnit (Xᵀ * V⁻¹ * X) ∧
      (Xᵀ * V⁻¹ * X)⁻¹ = Matrix.of (fun _ _ => v₁ * v₂ / (v₁ + v₂)) ∧
      glsMatrix X V = Matrix.of (fun _ i =>
        (![v₂ / (v₁ + v₂), v₁ / (v₁ + v₂)] : Fin 2 → ℝ) i) := by
  intro X V
  let a : ℝ := v₁⁻¹ + v₂⁻¹
  have ha : 0 < a := add_pos (inv_pos.mpr h₁) (inv_pos.mpr h₂)
  have hsum : 0 < v₁ + v₂ := add_pos h₁ h₂
  have hVinv : V⁻¹ = Matrix.diagonal ![v₁⁻¹, v₂⁻¹] := by
    apply Matrix.inv_eq_left_inv
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [V, Matrix.mul_apply, Fin.sum_univ_two, h₁.ne', h₂.ne']
  have hG : Xᵀ * V⁻¹ * X = Matrix.of (fun _ _ => a) := by
    rw [hVinv]
    ext i j
    fin_cases i
    fin_cases j
    simp [X, a, Matrix.mul_apply, Fin.sum_univ_two]
  have hunit : IsUnit (Xᵀ * V⁻¹ * X) := by
    rw [Matrix.isUnit_iff_isUnit_det, hG, Matrix.det_unique]
    exact isUnit_iff_ne_zero.mpr ha.ne'
  have hGinv : (Xᵀ * V⁻¹ * X)⁻¹ = Matrix.of (fun _ _ => v₁ * v₂ / (v₁ + v₂)) := by
    rw [hG]
    apply Matrix.inv_eq_left_inv
    ext i j
    fin_cases i
    fin_cases j
    simp [a, Matrix.mul_apply]
    field_simp [h₁.ne', h₂.ne', hsum.ne']
    exact add_comm v₂ v₁
  refine ⟨hunit, hGinv, ?_⟩
  rw [glsMatrix, hGinv, hVinv]
  ext i j
  fin_cases i
  fin_cases j <;>
    simp [X, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp [h₁.ne', h₂.ne', hsum.ne']

private theorem variance_weighted_meters {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {e₁ e₂ : Ω → ℝ} (h₁ : MemLp e₁ 2 P) (h₂ : MemLp e₂ 2 P)
    (θ a b : ℝ) :
    variance (fun ω => a * (θ + e₁ ω) + b * (θ + e₂ ω)) P =
      a ^ 2 * variance e₁ P + b ^ 2 * variance e₂ P + 2 * a * b * covariance e₁ e₂ P := by
  let u := fun ω => a * e₁ ω
  let w := fun ω => b * e₂ ω
  have hu : MemLp u 2 P := h₁.const_mul a
  have hw : MemLp w 2 P := h₂.const_mul b
  have heq : (fun ω => a * (θ + e₁ ω) + b * (θ + e₂ ω)) =
      fun ω => (a + b) * θ + (u + w) ω := by
    funext ω
    change a * (θ + e₁ ω) + b * (θ + e₂ ω) = (a + b) * θ + (a * e₁ ω + b * e₂ ω)
    ring
  rw [heq, variance_const_add (hu.add hw).aestronglyMeasurable]
  change variance (fun ω => u ω + w ω) P = _
  rw [variance_fun_add hu hw]
  simp only [u, w, variance_const_mul, covariance_const_mul_left, covariance_const_mul_right]
  ring

private theorem integral_weighted_meters {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {e₁ e₂ : Ω → ℝ} (he₁ : MemLp e₁ 2 P) (he₂ : MemLp e₂ 2 P)
    (θ a b : ℝ) :
    (∫ ω, a * (θ + e₁ ω) + b * (θ + e₂ ω) ∂P) =
      (a + b) * θ + (a * (∫ ω, e₁ ω ∂P) + b * (∫ ω, e₂ ω ∂P)) := by
  have hi₁ := (he₁.const_mul a).integrable one_le_two
  have hi₂ := (he₂.const_mul b).integrable one_le_two
  have hi : Integrable (fun ω => a * e₁ ω + b * e₂ ω) P := hi₁.add hi₂
  have heq : (fun ω => a * (θ + e₁ ω) + b * (θ + e₂ ω)) =
      fun ω => (a + b) * θ + (a * e₁ ω + b * e₂ ω) := by
    funext ω
    ring
  rw [heq, integral_add (integrable_const ((a + b) * θ)) hi, integral_const,
    integral_add hi₁ hi₂, integral_const_mul, integral_const_mul]
  simp only [probReal_univ, one_smul]

@[expose] public section

/-- For centered square-integrable errors, a linear combination of the two meter readings
with fixed weights `a` and `b` is unbiased for every parameter value exactly when `a + b = 1`. -/
lemma two_meter_linear_unbiased_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {e₁ e₂ : Ω → ℝ} (he₁ : MemLp e₁ 2 P) (he₂ : MemLp e₂ 2 P)
    (hm₁ : (∫ ω, e₁ ω ∂P) = 0) (hm₂ : (∫ ω, e₂ ω ∂P) = 0) {a b : ℝ} :
    (∀ t : ℝ, (∫ ω, a * (t + e₁ ω) + b * (t + e₂ ω) ∂P) = t) ↔ a + b = 1 := by
  simp only [integral_weighted_meters he₁ he₂, hm₁, hm₂, mul_zero, add_zero]
  exact ⟨fun h => by simpa only [mul_one] using h 1, fun h t => by rw [h, one_mul]⟩

/-- **Weighted reconciliation of two meters.** Let the two readings be `θ + e₁` and `θ + e₂`,
with square-integrable errors of positive variances `v₁` and `v₂`. The GLS estimate using the
intercept design and diagonal working covariance is `(v₂ * y₁ + v₁ * y₂) / (v₁ + v₂)`. It is
the unique minimizer of the sum of squared residuals weighted by the inverse variances.
Its bias is the same weighted average of the error means, so it is unbiased when both means
vanish; if only the first meter has mean error `β`, its bias is `v₂ * β / (v₁ + v₂)`.
With uncorrelated errors its variance is `v₁ * v₂ / (v₁ + v₂)`, at most either individual
variance and minimal among all linear estimators with weights summing to one. For centered
errors, these are exactly the linear estimators that are unbiased for every parameter value,
by `two_meter_linear_unbiased_iff`. With variances `1` and `4` and `e₂ = 2 * e₁`, the same
estimator has variance `36 / 25`, not `4 / 5`.

The minimality uses Aitken's theorem (A. C. Aitken, *On least squares and linear combination of
observations*, Proc. Roy. Soc. Edinburgh 55 (1936), 42–48). -/
theorem two_meter_reconciliation {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (θ : ℝ) {e₁ e₂ : Ω → ℝ} (he₁ : MemLp e₁ 2 P) (he₂ : MemLp e₂ 2 P)
    {v₁ v₂ : ℝ} (h₁ : 0 < v₁) (h₂ : 0 < v₂)
    (hv₁ : variance e₁ P = v₁) (hv₂ : variance e₂ P = v₂) :
    let X : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of fun _ _ => 1
    let V : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![v₁, v₂]
    let estimate := fun y₁ y₂ : ℝ => (v₂ * y₁ + v₁ * y₂) / (v₁ + v₂)
    let loss := fun y₁ y₂ x : ℝ => (y₁ - x) ^ 2 / v₁ + (y₂ - x) ^ 2 / v₂
    let E := fun ω => estimate (θ + e₁ ω) (θ + e₂ ω)
    (∀ y₁ y₂, (glsMatrix X V *ᵥ ![y₁, y₂]) 0 = estimate y₁ y₂) ∧
    (∀ y₁ y₂ x, x ≠ estimate y₁ y₂ → loss y₁ y₂ (estimate y₁ y₂) < loss y₁ y₂ x) ∧
    (∫ ω, E ω ∂P) - θ = (v₂ * (∫ ω, e₁ ω ∂P) + v₁ * (∫ ω, e₂ ω ∂P)) / (v₁ + v₂) ∧
    (covariance e₁ e₂ P = 0 →
      variance E P = v₁ * v₂ / (v₁ + v₂) ∧
      variance E P ≤ min v₁ v₂ ∧
      ∀ a : ℝ, variance E P ≤
        variance (fun ω => a * (θ + e₁ ω) + (1 - a) * (θ + e₂ ω)) P) ∧
    (v₁ = 1 → v₂ = 4 → e₂ = (fun ω => 2 * e₁ ω) → variance E P = 36 / 25) := by
  intro X V estimate loss E
  obtain ⟨hunit, hGinv, hGLS⟩ := twoMeter_gls_data h₁ h₂
  have hsum : 0 < v₁ + v₂ := add_pos h₁ h₂
  let a : ℝ := v₂ / (v₁ + v₂)
  let b : ℝ := v₁ / (v₁ + v₂)
  have hab : a + b = 1 := by
    change v₂ / (v₁ + v₂) + v₁ / (v₁ + v₂) = 1
    field_simp [hsum.ne']
    exact add_comm v₂ v₁
  have hE : E = fun ω => a * (θ + e₁ ω) + b * (θ + e₂ ω) := by
    funext ω
    dsimp only [E, estimate, a, b]
    ring
  have hvar := variance_weighted_meters he₁ he₂ θ a b
  rw [← hE, hv₁, hv₂] at hvar
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y₁ y₂
    change (glsMatrix _ _ *ᵥ ![y₁, y₂]) 0 = estimate y₁ y₂
    rw [hGLS]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, estimate]
    ring
  · intro y₁ y₂ x hx
    have hgap : loss y₁ y₂ x - loss y₁ y₂ (estimate y₁ y₂) =
        (v₁⁻¹ + v₂⁻¹) * (x - estimate y₁ y₂) ^ 2 := by
      dsimp only [loss, estimate]
      field_simp [h₁.ne', h₂.ne', hsum.ne']
      ring
    have hp := mul_pos (add_pos (inv_pos.mpr h₁) (inv_pos.mpr h₂))
      (sq_pos_of_ne_zero (sub_ne_zero.mpr hx))
    linarith
  · rw [hE, integral_weighted_meters he₁ he₂, hab, one_mul]
    dsimp only [a, b]
    ring
  · intro hcov
    have hV : V.PosDef := Matrix.PosDef.diagonal (by intro i; fin_cases i <;> assumption)
    have hmin (c : ℝ) : v₁ * v₂ / (v₁ + v₂) ≤ c ^ 2 * v₁ + (1 - c) ^ 2 * v₂ := by
      let A : Matrix (Fin 1) (Fin 2) ℝ := Matrix.of fun _ i => (![c, 1 - c] : Fin 2 → ℝ) i
      have hAX : A * X = 1 := by
        ext i j
        fin_cases i
        fin_cases j
        simp [A, X, Matrix.mul_apply, Fin.sum_univ_two]
      have hd := (aitken hV hunit A hAX).diag_nonneg (i := 0)
      rw [glsMatrix_mul_mul_transpose hV hunit, hGinv] at hd
      have hAV : (A * V * Aᵀ) 0 0 = c ^ 2 * v₁ + (1 - c) ^ 2 * v₂ := by
        simp [A, V, Matrix.mul_apply, Fin.sum_univ_two, Function.swap]
        ring
      simpa only [Matrix.sub_apply, Matrix.of_apply, hAV, sub_nonneg] using hd
    have hvarE : variance E P = v₁ * v₂ / (v₁ + v₂) := by
      rw [hvar, hcov, mul_zero, add_zero]
      dsimp only [a, b]
      field_simp [hsum.ne']
      ring
    refine ⟨hvarE, ?_, ?_⟩
    · rw [hvarE]
      exact le_min (by simpa using hmin 1) (by simpa using hmin 0)
    · intro c
      rw [hvarE, variance_weighted_meters he₁ he₂, hv₁, hv₂, hcov, mul_zero, add_zero]
      exact hmin c
  · rintro rfl rfl rfl
    have hEc : E = fun ω => θ + (6 / 5 : ℝ) * e₁ ω := by
      funext ω
      dsimp only [E, estimate]
      ring
    rw [hEc, variance_const_add (he₁.const_mul (6 / 5 : ℝ)).aestronglyMeasurable,
      variance_const_mul, hv₁]
    norm_num

/-- With centered, uncorrelated square-integrable errors of positive variances, the
inverse-variance estimate is unbiased for every parameter value and has variance no greater
than any fixed linear combination of the two readings that is unbiased for every parameter
value. The variance comparison holds at each parameter value. -/
theorem two_meter_reconciliation_min_variance {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {e₁ e₂ : Ω → ℝ} (he₁ : MemLp e₁ 2 P) (he₂ : MemLp e₂ 2 P)
    {v₁ v₂ : ℝ} (h₁ : 0 < v₁) (h₂ : 0 < v₂)
    (hv₁ : variance e₁ P = v₁) (hv₂ : variance e₂ P = v₂)
    (hm₁ : (∫ ω, e₁ ω ∂P) = 0) (hm₂ : (∫ ω, e₂ ω ∂P) = 0)
    (hcov : covariance e₁ e₂ P = 0) :
    let E := fun (t : ℝ) ω => (v₂ * (t + e₁ ω) + v₁ * (t + e₂ ω)) / (v₁ + v₂)
    (∀ t : ℝ, (∫ ω, E t ω ∂P) = t) ∧
      ∀ a b : ℝ, (∀ t : ℝ, (∫ ω, a * (t + e₁ ω) + b * (t + e₂ ω) ∂P) = t) →
        ∀ θ : ℝ, variance (E θ) P ≤ variance (fun ω => a * (θ + e₁ ω) + b * (θ + e₂ ω)) P := by
  intro E
  constructor
  · intro t
    have hbias := (two_meter_reconciliation t he₁ he₂ h₁ h₂ hv₁ hv₂).2.2.1
    change (∫ ω, E t ω ∂P) - t = _ at hbias
    simpa only [hm₁, hm₂, mul_zero, add_zero, zero_div, sub_eq_zero] using hbias
  · intro a b h_unbiased θ
    have hab := (two_meter_linear_unbiased_iff he₁ he₂ hm₁ hm₂).mp h_unbiased
    have hb : b = 1 - a := eq_sub_of_add_eq' hab
    subst b
    exact ((two_meter_reconciliation θ he₁ he₂ h₁ h₂ hv₁ hv₂).2.2.2.1 hcov).2.2 a

end

end MathlibExt.Probability.Statistics.GeneralizedLeastSquares
