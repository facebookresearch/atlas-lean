/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.PrenticePykeCaseControlWanted

open MeasureTheory

-- The unused assumptions are retained for compatibility with the original statement.
set_option linter.unusedVariables false in
set_option linter.unusedFintypeInType false in
/-- **Case-control sampling shifts only the logistic intercept** (Prentice and Pyke 1979). Let
`μ` be a probability measure on `Ω`, let `X : Ω → 𝒳` be a measurable covariate with values in
a finite type with measurable singletons and features `φ : 𝒳 → ℝ^K`, and let `D` (diseased)
and `S` (sampled) be measurable events. Assume:
* the logistic incidence model: `μ(D ∩ {X = x}) = σ(α + β ⬝ φ(x)) μ({X = x})` for every
  `x`;
* sampling depends on disease status only: `μ(S ∩ D ∩ {X = x}) = π₁ μ(D ∩ {X = x})` and
  `μ(S ∩ Dᶜ ∩ {X = x}) = π₀ μ(Dᶜ ∩ {X = x})` for every `x`, with sampling probabilities
  `0 < π₁ ≤ 1` and `0 < π₀ ≤ 1`.

Then for every covariate value `x` with `μ({X = x}) > 0`, the disease probability among the
sampled, `μ(D ∩ S ∩ {X = x}) / μ(S ∩ {X = x})`, equals `σ(α + log (π₁ / π₀) + β ⬝ φ(x))`.
Here `σ` is the logistic function `Real.sigmoid`.

Source: Prentice and Pyke (1979). -/
public theorem caseControl_logistic {Ω 𝒳 : Type*} [MeasurableSpace Ω] [Fintype 𝒳]
    [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] {K : ℕ} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → 𝒳) (hX : Measurable X) (φ : 𝒳 → Fin K → ℝ)
    (D S : Set Ω) (hD : MeasurableSet D) (hS : MeasurableSet S) (α : ℝ) (β : Fin K → ℝ)
    (π₀ π₁ : ℝ) (hπ₀ : 0 < π₀) (hπ₀' : π₀ ≤ 1) (hπ₁ : 0 < π₁) (hπ₁' : π₁ ≤ 1)
    (hlogit : ∀ x, μ.real (D ∩ X ⁻¹' {x}) = Real.sigmoid (α + β ⬝ᵥ φ x) * μ.real (X ⁻¹' {x}))
    (hcase : ∀ x, μ.real (S ∩ D ∩ X ⁻¹' {x}) = π₁ * μ.real (D ∩ X ⁻¹' {x}))
    (hcontrol : ∀ x, μ.real (S ∩ Dᶜ ∩ X ⁻¹' {x}) = π₀ * μ.real (Dᶜ ∩ X ⁻¹' {x}))
    (x : 𝒳) (hx : 0 < μ.real (X ⁻¹' {x})) :
    μ.real (D ∩ S ∩ X ⁻¹' {x}) / μ.real (S ∩ X ⁻¹' {x}) =
      Real.sigmoid (α + Real.log (π₁ / π₀) + β ⬝ᵥ φ x) := by
  let F := X ⁻¹' {x}
  let z := α + β ⬝ᵥ φ x
  have hF : μ.real (D ∩ F) + μ.real (Dᶜ ∩ F) = μ.real F := by
    simpa only [Set.sdiff_eq, Set.inter_comm] using
      (measureReal_inter_add_sdiff (μ := μ) (s := F) hD)
  have hSF : μ.real (S ∩ D ∩ F) + μ.real (S ∩ Dᶜ ∩ F) = μ.real (S ∩ F) := by
    simpa only [Set.sdiff_eq, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
      (measureReal_inter_add_sdiff (μ := μ) (s := S ∩ F) hD)
  have hDF : μ.real (D ∩ F) = Real.sigmoid z * μ.real F := hlogit x
  have hDcF : μ.real (Dᶜ ∩ F) = (1 - Real.sigmoid z) * μ.real F := by
    rw [hDF] at hF
    rw [sub_mul, one_mul, eq_sub_iff_add_eq]
    exact add_comm _ _ |>.trans hF
  let N := π₁ * Real.sigmoid z * μ.real F
  have hN : 0 < N := mul_pos (mul_pos hπ₁ (Real.sigmoid_pos z)) hx
  have hnum : μ.real (D ∩ S ∩ F) = N := by
    rw [Set.inter_comm D S, hcase x, hDF, ← mul_assoc]
  have hden : μ.real (S ∩ F) = N + π₀ * ((1 - Real.sigmoid z) * μ.real F) := by
    rw [← hSF, hcase x, hcontrol x, hDF, hDcF, ← mul_assoc π₁]
  have hshift : Real.exp (-(z + Real.log (π₁ / π₀))) = π₀ / π₁ * Real.exp (-z) := by
    rw [neg_add, Real.exp_add, Real.exp_neg (Real.log _),
      Real.exp_log (div_pos hπ₁ hπ₀), inv_div, mul_comm]
  have hfactor : π₀ * ((1 - Real.sigmoid z) * μ.real F) =
      N * Real.exp (-(z + Real.log (π₁ / π₀))) := by
    rw [hshift, ← Real.sigmoid_neg, ← Real.sigmoid_mul_rexp_neg]
    dsimp [N]
    field_simp [hπ₁.ne']
  have harg : α + Real.log (π₁ / π₀) + β ⬝ᵥ φ x = z + Real.log (π₁ / π₀) := by
    dsimp [z]
    ring
  change μ.real (D ∩ S ∩ F) / μ.real (S ∩ F) = _
  rw [hnum, hden, hfactor, harg, Real.sigmoid_def]
  calc
    N / (N + N * Real.exp (-(z + Real.log (π₁ / π₀)))) =
        N / (N * (1 + Real.exp (-(z + Real.log (π₁ / π₀))))) := by rw [mul_add, mul_one]
    _ = _ := by rw [div_mul_eq_div_div, div_self hN.ne', one_div]

end WantedExt.Biology.StatisticalGenetics.PrenticePykeCaseControlWanted
