/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Pi
public import MathlibExt.Probability.Statistics.FisherInformationIID

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.FisherInformationIID

open MeasureTheory

open scoped ENNReal

/-- Fixture A (through the main theorem): logistic-Bernoulli single-observation
information is `σ(θ₀)(1-σ(θ₀))`, so the joint n-sample information is `n·σ(θ₀)(1-σ(θ₀))`.
The logistic family is used because the plain Bernoulli family is not normalizable for
all real `θ` and cannot discharge `hprob`/`hnorm`.
The proof must establish `hS_int` and `hS2_int` from `hF` (not assume them): with
`σ = (1 + exp(-θ₀))⁻¹`, `score F θ₀ true = 1 - σ` and `score F θ₀ false = -σ` (via
`(hp_diff _).hasDerivAt.log`, as in L7-14 Fixture A), both bounded by 1 in absolute
value since `0 < σ < 1` from `hp_pos`, so `Integrable.of_bound` with `C = 1` (using
`hnorm` for the finite-measure instance) closes both. No new imports are needed for
this discharge (route probe-verified with the Atlas worktree toolchain; re-verify at
the pinned toolchain under step 6). -/
example (n : ℕ) (θ₀ : ℝ)
    (F : ℝ → Bool → ℝ)
    (hF : ∀ θ b, F θ b = if b then (1 + Real.exp (-θ))⁻¹ else 1 - (1 + Real.exp (-θ))⁻¹)
    (hI : MathlibExt.Probability.Statistics.FisherInformation.fisherInformation
      Measure.count F θ₀ =
      (1 + Real.exp (-θ₀))⁻¹ * (1 - (1 + Real.exp (-θ₀))⁻¹))
    (hnorm : IsProbabilityMeasure
      (MathlibExt.Probability.Statistics.FisherInformation.lawOf Measure.count F θ₀))
    (hmean : ∫ x, MathlibExt.Probability.Statistics.MLEAsymptoticNormality.score F θ₀ x ∂
      MathlibExt.Probability.Statistics.FisherInformation.lawOf Measure.count F θ₀ = 0) :
    MathlibExt.Probability.Statistics.FisherInformation.fisherInformation
        (Measure.pi fun _ : Fin n => (Measure.count : Measure Bool))
        (fun θ' x => ∏ i, F θ' (x i)) θ₀
      = n * ((1 + Real.exp (-θ₀))⁻¹ * (1 - (1 + Real.exp (-θ₀))⁻¹)) := by
  have he : 0 < Real.exp (-θ₀) := Real.exp_pos _
  have hD : 0 < 1 + Real.exp (-θ₀) := by linarith
  have hDne : (1 + Real.exp (-θ₀)) ≠ 0 := ne_of_gt hD
  have hσ0 : 0 < (1 + Real.exp (-θ₀))⁻¹ := inv_pos.mpr hD
  have hσ1 : (1 + Real.exp (-θ₀))⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by linarith : (1 : ℝ) < 1 + Real.exp (-θ₀))
  have hp_pos : ∀ x : Bool, 0 < F θ₀ x := by
    intro b
    cases b
    · have h : F θ₀ false = 1 - (1 + Real.exp (-θ₀))⁻¹ := by simp [hF]
      rw [h]
      exact sub_pos.mpr hσ1
    · have h : F θ₀ true = (1 + Real.exp (-θ₀))⁻¹ := by simp [hF]
      rw [h]
      exact hσ0
  have hp_meas : Measurable (F θ₀) := measurable_of_countable _
  have hneg : DifferentiableAt ℝ (fun t : ℝ => -t) θ₀ := differentiableAt_id.neg
  have hexp_neg : DifferentiableAt ℝ (fun t : ℝ => Real.exp (-t)) θ₀ := hneg.exp
  have hDe : DifferentiableAt ℝ (fun t : ℝ => 1 + Real.exp (-t)) θ₀ :=
    (differentiableAt_const 1).add hexp_neg
  have hσ : DifferentiableAt ℝ (fun t : ℝ => (1 + Real.exp (-t))⁻¹) θ₀ :=
    hDe.inv hDne
  have hp_diff : ∀ x : Bool, DifferentiableAt ℝ (fun t => F t x) θ₀ := by
    intro b
    cases b
    · have heq : (fun t => F t false) = (fun t => 1 - (1 + Real.exp (-t))⁻¹) := by
        funext t
        simp [hF]
      rw [heq]
      exact (differentiableAt_const 1).sub hσ
    · have heq : (fun t => F t true) = (fun t => (1 + Real.exp (-t))⁻¹) := by
        funext t
        simp [hF]
      rw [heq]
      exact hσ
  have h_neg : HasDerivAt (fun t : ℝ => -t) (-1) θ₀ := (hasDerivAt_id θ₀).neg
  have h_exp : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-θ₀) * -1) θ₀ :=
    (Real.hasDerivAt_exp (-θ₀)).comp θ₀ h_neg
  have h_add : HasDerivAt (fun t : ℝ => 1 + Real.exp (-t))
      (0 + Real.exp (-θ₀) * -1) θ₀ :=
    (hasDerivAt_const θ₀ 1).add h_exp
  have h_inv : HasDerivAt (fun t : ℝ => (1 + Real.exp (-t))⁻¹)
      (-(0 + Real.exp (-θ₀) * -1) / (1 + Real.exp (-θ₀)) ^ 2) θ₀ :=
    h_add.inv hDne
  have hD2 : (1 + Real.exp (-θ₀)) ^ 2 ≠ 0 := pow_ne_zero 2 hDne
  have hσ'_eq : -(0 + Real.exp (-θ₀) * -1) / (1 + Real.exp (-θ₀)) ^ 2
      = (1 + Real.exp (-θ₀))⁻¹ * (1 - (1 + Real.exp (-θ₀))⁻¹) := by
    have h1m : 1 - (1 + Real.exp (-θ₀))⁻¹
        = Real.exp (-θ₀) / (1 + Real.exp (-θ₀)) := by
      field_simp
      ring
    rw [h1m]
    field_simp
    ring
  have hderiv_σ : deriv (fun t : ℝ => (1 + Real.exp (-t))⁻¹) θ₀
      = (1 + Real.exp (-θ₀))⁻¹ * (1 - (1 + Real.exp (-θ₀))⁻¹) := by
    rw [h_inv.deriv]
    exact hσ'_eq
  have hs_true : MathlibExt.Probability.Statistics.MLEAsymptoticNormality.score F θ₀ true
      = 1 - (1 + Real.exp (-θ₀))⁻¹ := by
    have hlog : MathlibExt.Probability.Statistics.MLEAsymptoticNormality.score F θ₀ true
        = deriv (fun t => F t true) θ₀ / F θ₀ true :=
      ((hp_diff true).hasDerivAt.log (hp_pos true).ne').deriv
    have hFtrue : F θ₀ true = (1 + Real.exp (-θ₀))⁻¹ := by simp [hF]
    have hFderiv : deriv (fun t => F t true) θ₀
        = (1 + Real.exp (-θ₀))⁻¹ * (1 - (1 + Real.exp (-θ₀))⁻¹) := by
      have heq : (fun t => F t true) = (fun t => (1 + Real.exp (-t))⁻¹) := by
        funext t
        simp [hF]
      rw [heq]
      exact hderiv_σ
    have hσne : (1 + Real.exp (-θ₀))⁻¹ ≠ 0 := inv_ne_zero hDne
    rw [hlog, hFderiv, hFtrue]
    exact mul_div_cancel_left₀ _ hσne
  have hs_false : MathlibExt.Probability.Statistics.MLEAsymptoticNormality.score F θ₀ false
      = -(1 + Real.exp (-θ₀))⁻¹ := by
    have hlog : MathlibExt.Probability.Statistics.MLEAsymptoticNormality.score F θ₀ false
        = deriv (fun t => F t false) θ₀ / F θ₀ false :=
      ((hp_diff false).hasDerivAt.log (hp_pos false).ne').deriv
    have hFfalse : F θ₀ false = 1 - (1 + Real.exp (-θ₀))⁻¹ := by simp [hF]
    have hFderiv : deriv (fun t => F t false) θ₀
        = -((1 + Real.exp (-θ₀))⁻¹ * (1 - (1 + Real.exp (-θ₀))⁻¹)) := by
      have heq : (fun t => F t false) = (fun t => 1 - (1 + Real.exp (-t))⁻¹) := by
        funext t
        simp [hF]
      rw [heq]
      have hd : deriv (fun t => 1 - (1 + Real.exp (-t))⁻¹) θ₀
          = deriv (fun _ => (1 : ℝ)) θ₀ - deriv (fun t => (1 + Real.exp (-t))⁻¹) θ₀ :=
        deriv_sub (differentiableAt_const 1) hσ
      rw [hd, deriv_const, hderiv_σ]
      ring
    have h1mσne : 1 - (1 + Real.exp (-θ₀))⁻¹ ≠ 0 :=
      ne_of_gt (sub_pos.mpr hσ1)
    rw [hlog, hFderiv, hFfalse, div_eq_iff h1mσne]
    ring
  have := hnorm
  have haesm_S : AEStronglyMeasurable
      (MathlibExt.Probability.Statistics.MLEAsymptoticNormality.score F θ₀)
      (MathlibExt.Probability.Statistics.FisherInformation.lawOf Measure.count F θ₀) :=
    (measurable_of_countable _).aestronglyMeasurable
  have hbS : ∀ᵐ x ∂(MathlibExt.Probability.Statistics.FisherInformation.lawOf
      Measure.count F θ₀),
      ‖MathlibExt.Probability.Statistics.MLEAsymptoticNormality.score F θ₀ x‖ ≤ (1 : ℝ) := by
    apply Filter.Eventually.of_forall
    intro b
    cases b
    · rw [hs_false, Real.norm_eq_abs, abs_neg, abs_of_pos hσ0]
      exact le_of_lt hσ1
    · rw [hs_true, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hσ1)]
      linarith [hσ0]
  have hS_int : Integrable
      (MathlibExt.Probability.Statistics.MLEAsymptoticNormality.score F θ₀)
      (MathlibExt.Probability.Statistics.FisherInformation.lawOf Measure.count F θ₀) :=
    Integrable.of_bound haesm_S 1 hbS
  have haesm_S2 : AEStronglyMeasurable
      (fun x => (MathlibExt.Probability.Statistics.MLEAsymptoticNormality.score F θ₀ x) ^ 2)
      (MathlibExt.Probability.Statistics.FisherInformation.lawOf Measure.count F θ₀) :=
    (measurable_of_countable _).aestronglyMeasurable
  have hbS2 : ∀ᵐ x ∂(MathlibExt.Probability.Statistics.FisherInformation.lawOf
      Measure.count F θ₀),
      ‖(MathlibExt.Probability.Statistics.MLEAsymptoticNormality.score F θ₀ x) ^ 2‖ ≤ (1 : ℝ) := by
    apply Filter.Eventually.of_forall
    intro b
    cases b
    · rw [hs_false, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [hσ0, hσ1]
    · rw [hs_true, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [hσ0, hσ1]
  have hS2_int : Integrable
      (fun x => (MathlibExt.Probability.Statistics.MLEAsymptoticNormality.score F θ₀ x) ^ 2)
      (MathlibExt.Probability.Statistics.FisherInformation.lawOf Measure.count F θ₀) :=
    Integrable.of_bound haesm_S2 1 hbS2
  have hmain := MathlibExt.Probability.Statistics.FisherInformation.fisherInformation_iid
    n hp_pos hp_meas hp_diff hnorm hmean hS_int hS2_int
  rw [hmain, hI]

/-- Fixture B (boundary): at `n = 0` the joint information is zero. -/
example {𝓧 : Type*} [MeasurableSpace 𝓧]
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ : ℝ} :
    MathlibExt.Probability.Statistics.FisherInformation.fisherInformation
        (Measure.pi fun _ : Fin 0 => ν)
        (fun θ' x => ∏ i, p θ' (x i)) θ = 0 := by
  have h1 : ∀ x : Fin 0 → 𝓧, (fun θ' => ∏ i, p θ' (x i)) = fun _ => 1 := by
    intro x
    funext θ'
    exact Fin.prod_univ_zero _
  have h2 : ∀ x : Fin 0 → 𝓧, deriv (fun θ' => ∏ i, p θ' (x i)) θ = 0 := by
    intro x
    rw [h1 x]
    exact deriv_const θ 1
  show (∫ x, deriv (fun θ' => ∏ i, p θ' (x i)) θ ^ 2 / (∏ i, p θ (x i))
    ∂(Measure.pi fun _ : Fin 0 => ν)) = 0
  have h3 : (fun x : Fin 0 → 𝓧 =>
      deriv (fun θ' => ∏ i, p θ' (x i)) θ ^ 2 / (∏ i, p θ (x i))) = fun _ => 0 := by
    funext x
    rw [h2 x]
    simp
  rw [h3]
  exact integral_zero _ _

/-- Fixture C (use, through the main theorem): at `n = 1` the joint information is the
single-observation information. -/
example {𝓧 : Type*} [MeasurableSpace 𝓧]
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ : ℝ}
    (hp_pos : ∀ x, 0 < p θ x) (hp_meas : Measurable (p θ))
    (hp_diff : ∀ x, DifferentiableAt ℝ (fun t => p t x) θ)
    (hnorm : IsProbabilityMeasure
      (MathlibExt.Probability.Statistics.FisherInformation.lawOf ν p θ))
    (hmean : ∫ x, MathlibExt.Probability.Statistics.MLEAsymptoticNormality.score p θ x ∂
      MathlibExt.Probability.Statistics.FisherInformation.lawOf ν p θ = 0)
    (hS_int : Integrable
      (MathlibExt.Probability.Statistics.MLEAsymptoticNormality.score p θ)
      (MathlibExt.Probability.Statistics.FisherInformation.lawOf ν p θ))
    (hS2_int : Integrable
      (fun x => (MathlibExt.Probability.Statistics.MLEAsymptoticNormality.score p θ x) ^ 2)
      (MathlibExt.Probability.Statistics.FisherInformation.lawOf ν p θ)) :
    MathlibExt.Probability.Statistics.FisherInformation.fisherInformation
        (Measure.pi fun _ : Fin 1 => ν)
        (fun θ' x => ∏ i, p θ' (x i)) θ
      = MathlibExt.Probability.Statistics.FisherInformation.fisherInformation ν p θ := by
  have h := MathlibExt.Probability.Statistics.FisherInformation.fisherInformation_iid
    1 hp_pos hp_meas hp_diff hnorm hmean hS_int hS2_int
  simpa using h

end MathlibExtTest.Probability.Statistics.FisherInformationIID
