/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Renewal.ExpKeyRenewal

import MathlibExt.Probability.Distributions.ExponentialMoments
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Tests for the `Exp(1)` key renewal theorem

Non-vacuity of `keyRenewal_expMeasure_one`: the pair `y t = 1_{t ≥ 0} e^{-t}`,
`Y t = 1_{t ≥ 0}` is `KeyRenewalAdmissible`, solves the `Exp(1)` renewal
equation (checked from the convolution, `e^{-t} + (1 - e^{-t}) = 1`), and the
theorem's limit `(∫_{(0,∞)} e^{-s} ds) / 1` evaluates to `1 = lim Y`.

Non-vacuity of the family corollary: for every `θ > 0`, the exact tail
`Z t = 1_{t ≥ 0} (1 + θ)⁻¹ e^{-θ t}` solves the renewal equation of
`G_θ = (1 + θ)⁻¹ · Exp(1 + θ)`, so `tendsto_scaled_cramerLundberg_expFamily`
applies with all hypotheses discharged, and its constant `(1 + θ)⁻¹` agrees with
`e^{θ t} Z t = (1 + θ)⁻¹`. Boundary: at `θ = 0` the family member is the proper
law `Exp(1)` and its tilt is still `Exp(1)`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Real ProbabilityTheory

namespace MathlibExtTest.Probability.Renewal.ExpKeyRenewal

open MathlibExt.Probability.Renewal.LatticeConstants
open MathlibExt.Probability.Renewal.ExpKeyRenewal

/-! ### The pair `y = 1_{t ≥ 0} e^{-t}`, `Y = 1_{t ≥ 0}` -/

/-- Input `y t = 1_{t ≥ 0} e^{-t}`. -/
private noncomputable def yex : ℝ → ℝ := (Ici 0).indicator (fun t => exp (-t))

/-- Solution `Y t = 1_{t ≥ 0}`. -/
private noncomputable def Yex : ℝ → ℝ := (Ici 0).indicator (fun _ => 1)

private lemma notMem_Ici_of_neg {t : ℝ} (ht : t < 0) : t ∉ Ici (0 : ℝ) :=
  fun h => absurd (mem_Ici.1 h) (not_le.2 ht)

private lemma Yex_neg : ∀ t < 0, Yex t = 0 := fun _ ht =>
  indicator_of_notMem (notMem_Ici_of_neg ht) _

private lemma yex_admissible : KeyRenewalAdmissible Yex yex := by
  refine ⟨(by fun_prop : Measurable fun t : ℝ => exp (-t)).indicator measurableSet_Ici,
    fun t ht => indicator_of_notMem (notMem_Ici_of_neg ht) _, ?_, ?_,
    measurable_const.indicator measurableSet_Ici, Yex_neg, fun _ => ⟨1, fun t _ => ?_⟩⟩
  · -- Continuous away from `0`.
    refine ((countable_singleton (0 : ℝ)).ae_notMem volume).mono fun t ht => ?_
    rcases lt_or_gt_of_ne (show t ≠ 0 from ht) with hneg | hpos
    · refine (continuousAt_const (y := (0 : ℝ))).congr
        (eventually_of_mem (Iio_mem_nhds hneg) fun s hs => ?_)
      exact (indicator_of_notMem (notMem_Ici_of_neg hs) (fun t : ℝ => exp (-t))).symm
    · refine (by fun_prop : Continuous fun s : ℝ => exp (-s)).continuousAt.congr
        (eventually_of_mem (Ioi_mem_nhds hpos) fun s hs => ?_)
      exact (indicator_of_mem (mem_Ici.2 (le_of_lt hs)) (fun t : ℝ => exp (-t))).symm
  · refine ⟨fun t => exp (-t), fun a b hab => exp_le_exp.2 (by linarith),
      (integrableOn_Ici_iff_integrableOn_Ioi).2 (integrableOn_exp_neg_Ioi 0), fun t ht => ?_⟩
    rw [yex, indicator_of_mem (mem_Ici.2 ht), abs_of_pos (exp_pos _)]
  · by_cases ht : t ∈ Ici (0 : ℝ) <;> simp [Yex, ht]

private lemma Yex_renewal : ∀ t, Yex t = yex t + ∫ x, Yex (t - x) ∂(expMeasure 1) := by
  intro t
  rcases lt_or_ge t 0 with ht | ht
  · rw [integral_expMeasure_eq_setIntegral one_pos,
      setIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0) fun x hx => by
        simp only
        rw [Yex_neg _ (by linarith [mem_Ioi.1 hx]), mul_zero],
      integral_zero, Yex_neg t ht, yex, indicator_of_notMem (notMem_Ici_of_neg ht), add_zero]
  · rw [integral_expMeasure_one_sub Yex_neg ht,
      intervalIntegral.integral_congr (g := fun s => exp s) fun s hs => by
        rw [uIcc_of_le ht] at hs
        simp [Yex, indicator_of_mem (mem_Ici.2 hs.1)],
      integral_exp, exp_zero, Yex, yex, indicator_of_mem (mem_Ici.2 ht),
      indicator_of_mem (mem_Ici.2 ht), mul_sub, ← exp_add, neg_add_cancel, exp_zero, mul_one]
    ring

-- `keyRenewal_expMeasure_one` applies to the pair.
example : Tendsto Yex atTop (𝓝 ((∫ s in Ioi 0, yex s) / ∫ x, x ∂(expMeasure 1))) :=
  keyRenewal_expMeasure_one Yex yex yex_admissible Yex_renewal

-- The theorem's constant, computed from the definitions, is `1`.
example : (∫ s in Ioi 0, yex s) / ∫ x, x ∂(expMeasure 1) = 1 := by
  rw [integral_id_expMeasure one_pos, inv_one, div_one,
    setIntegral_congr_fun measurableSet_Ioi (g := fun s => exp (-s)) fun s hs =>
      indicator_of_mem (mem_Ici.2 (le_of_lt hs)) _,
    integral_exp_neg_Ioi_zero]

-- ... and agrees with the direct limit: `Y t = 1` for `t ≥ 0`.
example : Tendsto Yex atTop (𝓝 1) :=
  tendsto_const_nhds.congr' ((eventually_ge_atTop 0).mono fun _ ht =>
    (indicator_of_mem (mem_Ici.2 ht) _).symm)

-- The explicit solution `Y t = y t + ∫_0^t y` at `t = 2`.
example : Yex 2 = yex 2 + ∫ s in (0 : ℝ)..2, yex s :=
  eq_add_intervalIntegral_of_renewal_expMeasure_one yex_admissible.2.2.1
    yex_admissible.2.2.2.2.1 Yex_neg yex_admissible.2.2.2.2.2.2 Yex_renewal (by norm_num)

/-! ### The family `G_θ = (1 + θ)⁻¹ · Exp(1 + θ)`, exact tail `(1 + θ)⁻¹ e^{-θ t}` -/

/-- The family member `G_θ`. -/
private noncomputable abbrev Gθ (θ : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 + θ)⁻¹ • expMeasure (1 + θ)

/-- The exact strict tail `Z t = 1_{t ≥ 0} (1 + θ)⁻¹ e^{-θ t}`. -/
private noncomputable def Zθ (θ : ℝ) : ℝ → ℝ :=
  (Ici 0).indicator (fun t => (1 + θ)⁻¹ * exp (-(θ * t)))

private lemma Zθ_neg (θ : ℝ) : ∀ t < 0, Zθ θ t = 0 := fun _ ht =>
  indicator_of_notMem (notMem_Ici_of_neg ht) _

private lemma Zθ_measurable (θ : ℝ) : Measurable (Zθ θ) :=
  (by fun_prop : Measurable fun t : ℝ => (1 + θ)⁻¹ * exp (-(θ * t))).indicator measurableSet_Ici

private lemma Zθ_bdd {θ : ℝ} (hθ : 0 < θ) : ∃ M, ∀ t, |Zθ θ t| ≤ M := by
  refine ⟨1, fun t => ?_⟩
  by_cases ht : t ∈ Ici (0 : ℝ)
  · rw [Zθ, indicator_of_mem ht, abs_of_pos (by positivity)]
    have h1 : exp (-(θ * t)) ≤ 1 := exp_le_one_iff.2 (by nlinarith [mem_Ici.1 ht])
    have h2 : (1 + θ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    nlinarith [exp_pos (-(θ * t))]
  · rw [Zθ, indicator_of_notMem ht, abs_zero]
    exact zero_le_one

private lemma Gθ_tail {θ : ℝ} (hθ : 0 < θ) {s : ℝ} (hs : 0 ≤ s) :
    (Gθ θ).real (Ioi s) = (1 + θ)⁻¹ * exp (-((1 + θ) * s)) := by
  have hr : 0 < 1 + θ := by linarith
  rw [← integral_indicator_one measurableSet_Ioi, integral_expFamily (by linarith)]
  have : ∀ y, exp (-((1 + θ) * y)) * (Ioi s).indicator 1 y =
      (Ioi s).indicator (fun y => exp ((-(1 + θ)) * y)) y := fun y => by
    by_cases hy : y ∈ Ioi s
    · simp only [hy, indicator_of_mem, Pi.one_apply, mul_one]
      ring_nf
    · simp [hy]
  simp_rw [this]
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_right.2 hs,
    integral_exp_mul_Ioi (by linarith)]
  field_simp

private lemma Zθ_renewal {θ : ℝ} (hθ : 0 < θ) :
    ∀ t, Zθ θ t = (Ici 0).indicator (fun s => (Gθ θ).real (Ioi s)) t +
      ∫ y, Zθ θ (t - y) ∂(Gθ θ) := by
  intro t
  rw [integral_expFamily (by linarith)]
  rcases lt_or_ge t 0 with ht | ht
  · have hz : ∀ y ∈ Ioi (0 : ℝ), exp (-((1 + θ) * y)) * Zθ θ (t - y) = 0 := fun y hy => by
      rw [Zθ_neg θ _ (by linarith [mem_Ioi.1 hy]), mul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi hz, integral_zero, Zθ_neg θ t ht,
      indicator_of_notMem (notMem_Ici_of_neg ht), add_zero]
  · have hcut : ∀ y, exp (-((1 + θ) * y)) * Zθ θ (t - y) =
        (Iic t).indicator (fun y => (1 + θ)⁻¹ * exp (-(θ * t)) * exp (-1 * y)) y := fun y => by
      by_cases hy : y ∈ Iic t
      · have : t - y ∈ Ici (0 : ℝ) := mem_Ici.2 (by have := mem_Iic.1 hy; linarith)
        rw [indicator_of_mem hy, Zθ, indicator_of_mem this, mul_left_comm, mul_assoc,
          ← exp_add, ← exp_add]
        congr 2
        ring
      · have : t - y ∉ Ici (0 : ℝ) := fun h => hy (mem_Iic.2 (by have := mem_Ici.1 h; linarith))
        rw [indicator_of_notMem hy, Zθ, indicator_of_notMem this, mul_zero]
    simp_rw [hcut]
    rw [setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic, integral_const_mul,
      ← intervalIntegral.integral_of_le ht,
      intervalIntegral.integral_comp_mul_left (fun y => exp y) (by norm_num : (-1 : ℝ) ≠ 0),
      integral_exp, Zθ, indicator_of_mem (mem_Ici.2 ht), indicator_of_mem (mem_Ici.2 ht),
      Gθ_tail hθ ht]
    have : exp (-((1 + θ) * t)) = exp (-(θ * t)) * exp (-t) := by rw [← exp_add]; ring_nf
    rw [this]
    simp only [mul_zero, exp_zero, smul_eq_mul, neg_mul, one_mul]
    ring

-- `hKRT` holds for every member of the family with `θ > -1`.
example {θ : ℝ} (hθ : -1 < θ) : ∀ Y y : ℝ → ℝ, KeyRenewalAdmissible Y y →
    (∀ t, Y t = y t + ∫ x, Y (t - x) ∂((Gθ θ).tilted (fun x => θ * x))) →
    Tendsto Y atTop (𝓝 ((∫ s in Ioi 0, y s) / ∫ x, x ∂((Gθ θ).tilted (fun x => θ * x)))) :=
  keyRenewal_of_tilted_eq_expMeasure_one (tilted_expFamily_eq_expMeasure_one hθ)

-- The unconditional Cramér–Lundberg limit for the family, all hypotheses discharged.
example {θ : ℝ} (hθ : 0 < θ) : Tendsto (fun t => exp (θ * t) * Zθ θ t) atTop (𝓝 (1 + θ)⁻¹) :=
  tendsto_scaled_cramerLundberg_expFamily hθ (Zθ_measurable θ) (Zθ_neg θ) (Zθ_bdd hθ)
    (Zθ_renewal hθ)

-- Its constant agrees with the exact tail: `e^{θ t} Z t = (1 + θ)⁻¹` for `t ≥ 0`.
example {θ : ℝ} : Tendsto (fun t => exp (θ * t) * Zθ θ t) atTop (𝓝 (1 + θ)⁻¹) := by
  refine tendsto_const_nhds.congr' ((eventually_ge_atTop 0).mono fun t ht => ?_)
  show (1 + θ)⁻¹ = exp (θ * t) * Zθ θ t
  rw [Zθ, indicator_of_mem (mem_Ici.2 ht), mul_left_comm, ← exp_add, add_neg_cancel, exp_zero,
    mul_one]

-- At `θ = 1` the family member has mass `½`, straight from `measure_univ` of `Exp(2)`.
example : (Gθ 1).real univ = 1 / 2 := by
  have := isProbabilityMeasure_expMeasure (show (0 : ℝ) < 1 + 1 by norm_num)
  show (ENNReal.ofReal (1 + 1 : ℝ)⁻¹ • expMeasure (1 + 1)).real univ = 1 / 2
  rw [measureReal_def, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one,
    ENNReal.toReal_ofReal (by norm_num)]
  norm_num

-- At `θ = 1` the Cramér–Lundberg constant is `½`: `e^{t} Z t → ½`.
example : Tendsto (fun t => exp (1 * t) * Zθ 1 t) atTop (𝓝 (1 / 2)) := by
  have h := tendsto_scaled_cramerLundberg_expFamily one_pos (Zθ_measurable 1) (Zθ_neg 1)
    (Zθ_bdd one_pos) (Zθ_renewal one_pos)
  rwa [show (1 + 1 : ℝ)⁻¹ = 1 / 2 by norm_num] at h

-- Boundary `θ = 0`: the proper law `Exp(1)` is its own Cramér tilt.
example : (Gθ 0).tilted (fun x => 0 * x) = expMeasure 1 :=
  tilted_expFamily_eq_expMeasure_one (by norm_num)

end MathlibExtTest.Probability.Renewal.ExpKeyRenewal
